"""Rebuild attributed standalone manuscripts; preserve all reviewed source content."""
import hashlib,os,re,shutil,subprocess,tempfile
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
ROOT=Path(__file__).resolve().parents[1]
def expand(path,review):
 text=path.read_text(encoding='utf-8')
 assert hashlib.sha256(text.encode()).hexdigest() in review,path
 return re.sub(r'\\input\{([^}]+)\}',lambda m:'% BEGIN INPUT '+m[1]+'\n'+expand(path.parent/m[1],review)+'\n% END INPUT '+m[1],text)
def prepare(ident):
 if ident=='AA-01':
  source=ROOT/'submitted/AA01_submission/manuscript.tex';review=(ROOT/'verification/reviews/AA-01-review.md').read_text(encoding='utf-8')
  assert hashlib.sha256(source.read_text(encoding='utf-8').encode()).hexdigest() in (ROOT/'verification/reviews/AA-01-second-review.md').read_text(encoding='utf-8')
  notice='Independently reviewed resolution of the exact canonical finite-tree model. The supplied work is AI-assisted. Two independent agent reviews verify the mathematical argument. The experimental programs described in the original text were not retained: their reported counts, solver runs and compiled budgets have not been reproduced or certified here. Only two original JSON logs survive. This export uses the complete reviewed TeX, which includes material added after the supplied PDF was built.'
 else:
  source=ROOT/'submitted/NLA_partial_results_submission_package/manuscript.tex';review=(ROOT/'verification/reviews/AC-11-12-review.md').read_text(encoding='utf-8')
  notice='Independently reviewed finite-case results: AC-11 through order 35 and AC-12 through order 10. Both universal targets remain partially resolved. The supplied work is AI-assisted. The analytic review and fresh exact certificate checks are recorded separately in the submission record.'
 assert 'PASS' in review
 body=expand(source,review)
 byline=r'{\large Matthew J. Colbrook}\\[3pt]{\small Department of Applied Mathematics and Theoretical Physics}\\{\small University of Cambridge, Cambridge, United Kingdom}\\{\small\href{mailto:m.colbrook@damtp.cam.ac.uk}{m.colbrook@damtp.cam.ac.uk}}\\[5pt]{\small 11 September 2026}'
 notice=r'\noindent\textbf{Submission and verification update (11 September 2026).} '+notice+' The dated reports supersede original pending-review remarks. Independent agent review is not external human peer review or formal certification; no novelty or priority claim is made. See the '+r'\href{https://github.com/MColbrook/OpenProblemsInNLA/tree/codex/colbrook-arithmetic-submissions/references/colbrook-arithmetic-2026-09-11}{submission record}.'+'\n\\par\\medskip\n'
 if ident=='AA-01':
  body=body.replace(r'\end{center}',r'\par\medskip '+byline+'\n'+r'\end{center}'+'\n'+notice,1)
 else:
  body=body.replace(r'\author{}',r'\author{'+byline+'}',1).replace(r'\date{}',r'\date{}',1)
  body=body.replace(r'\maketitle',r'\maketitle'+'\n'+notice,1)
 layout=(r'\geometry{margin=24mm}'+'\n') if ident!='AA-01' else ''
 body=body.replace(r'\begin{document}',layout+r'\hypersetup{pdfauthor={Matthew J. Colbrook}}'+'\n'+r'\setlength{\emergencystretch}{3em}'+'\n'+r'\begin{document}',1)
 return body
def render(ident):
 tex=prepare(ident);out=ROOT/'manuscripts';out.mkdir(exist_ok=True)
 with tempfile.TemporaryDirectory(prefix='nla-arithmetic-') as d:
  p=Path(d);(p/'manuscript.tex').write_text(tex,encoding='utf-8')
  for _ in range(2):
   r=subprocess.run([os.environ.get('XELATEX','xelatex'),'-interaction=nonstopmode','-halt-on-error','manuscript.tex'],cwd=p,capture_output=True,text=True,encoding='utf-8',errors='replace')
   if r.returncode:raise RuntimeError(r.stdout[-5000:])
  log=(p/'manuscript.log').read_text(encoding='utf-8',errors='replace');warnings=re.findall(r'(?:Overfull[^\n]+|Missing character[^\n]+|[^\n]*undefined[^\n]*)',log)
  (out/(ident+'.tex')).write_text(tex,encoding='utf-8');shutil.copyfile(p/'manuscript.pdf',out/(ident+'.pdf'))
 return ident,warnings
if __name__=='__main__':
 with ThreadPoolExecutor(max_workers=2) as pool:
  for ident,warnings in pool.map(render,['AA-01','AC-11-12']):print(ident+': '+('; '.join(warnings) if warnings else 'OK'),flush=True)
