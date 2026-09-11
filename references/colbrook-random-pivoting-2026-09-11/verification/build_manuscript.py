"""Build an attributed copy after complete-source independent review."""
import hashlib,os,re,shutil,subprocess,tempfile
from pathlib import Path
root=Path(__file__).resolve().parents[1]
source=root/'submitted/manuscript/sharp_random_pivoting.tex'
original=source.read_text(encoding='utf-8');digest=hashlib.sha256(original.encode()).hexdigest()
for ident in ['RA-02','RA-03']:
 report=(root/'verification/reviews'/f'{ident}-review.md').read_text(encoding='utf-8');assert digest in report and 'PASS' in report
text=original.replace(r'\author{}',r'\author{Matthew J. Colbrook\thanks{Department of Applied Mathematics and Theoretical Physics, University of Cambridge, Cambridge, United Kingdom. Email: m.colbrook@damtp.cam.ac.uk.}}',1).replace(r'\date{}',r'\date{11 September 2026}',1)
text=text.replace(r'\begin{document}',r'\hypersetup{pdfauthor={Matthew J. Colbrook}}'+'\n'+r'\usepackage{xurl}'+'\n'+r'\begin{document}',1).replace(r'\vspace{-2.2em}','',1)
notice=r'''\begin{quote}\small
Authorship is recorded at the submitter's request. This manuscript was developed with AI assistance. Independent agents checked the complete source against RA-02 and RA-03; exact verification was rerun separately. This is not external human peer review or formal certification, and no priority claim is made. The original archive's eligibility hold and failed-access remarks are historical: the live repository checks and submission record accompany this authored edition.
\end{quote}
'''
text=text.replace(r'\begin{abstract}',notice+r'\begin{abstract}',1)
marker=r'\begin{abstract}';assert original[original.index(marker):]==text[text.index(marker):]
with tempfile.TemporaryDirectory(prefix='nla-random-pivoting-') as d:
 p=Path(d);(p/'manuscript.tex').write_text(text,encoding='utf-8')
 for _ in range(2):
  result=subprocess.run([os.environ.get('XELATEX','xelatex'),'-interaction=nonstopmode','-halt-on-error','manuscript.tex'],cwd=p,capture_output=True,text=True,encoding='utf-8',errors='replace')
  if result.returncode:raise RuntimeError(result.stdout[-5000:])
 log=(p/'manuscript.log').read_text(encoding='utf-8',errors='replace');warnings=re.findall(r'(?:Overfull[^\n]+|Missing character[^\n]+|[^\n]*undefined[^\n]*)',log)
 (root/'manuscripts/sharp_random_pivoting.tex').write_text(text,encoding='utf-8');shutil.copyfile(p/'manuscript.pdf',root/'manuscripts/sharp_random_pivoting.pdf')
 print('PDF: '+('; '.join(warnings) if warnings else 'OK'))
