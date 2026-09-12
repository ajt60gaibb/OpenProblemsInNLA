"""Build attributed editions; preserve the reviewed abstract-through-end source."""
import hashlib, os, re, shutil, subprocess, tempfile
from pathlib import Path
root=Path(__file__).resolve().parents[1]
for folder,stem,review in [('TR-17','tr17_solution','TR-17-review.md'),('TR-27','tr27_solution','TR-27-review.md')]:
    original=(root/'submitted'/folder/'solution.tex').read_text(encoding='utf-8')
    digest=hashlib.sha256(original.encode()).hexdigest()
    report=(root/'verification/reviews'/review).read_text(encoding='utf-8')
    assert digest in report and 'PASS' in report
    text=original.replace(r'\author{}',r'\author{Matthew J. Colbrook\thanks{Department of Applied Mathematics and Theoretical Physics, University of Cambridge, Cambridge, United Kingdom. Email: m.colbrook@damtp.cam.ac.uk.}}',1).replace(r'\date{}',r'\date{11 September 2026}',1)
    text=text.replace(r'\begin{document}',r'\hypersetup{pdfauthor={Matthew J. Colbrook}}'+'\n'+r'\usepackage{xurl}'+'\n'+r'\begin{document}',1).replace(r'\vspace{-2.5em}','',1).replace(r'\begin{center}\small Proposed resolution; pending independent mathematical review.\end{center}', '',1)
    notice=r'''\begin{quote}\small
Authorship is recorded at the submitter's request. AI assistance is disclosed. An independent agent reviewed this complete mathematical source against the original repository targets; a separate agent checked the accompanying computations. This is not external human peer review or formal certification, and no priority claim is made. The original proposed manuscripts have now passed independent review; reports and live eligibility checks accompany this attributed edition.
\end{quote}
'''
    text=text.replace(r'\begin{abstract}',notice+r'\begin{abstract}',1)
    marker=r'\begin{abstract}'
    assert original[original.index(marker):]==text[text.index(marker):]
    with tempfile.TemporaryDirectory(prefix='nla-jsr-growth-') as d:
        p=Path(d);(p/'manuscript.tex').write_text(text,encoding='utf-8')
        for _ in range(2):
            result=subprocess.run([os.environ.get('XELATEX','xelatex'),'-interaction=nonstopmode','-halt-on-error','manuscript.tex'],cwd=p,capture_output=True,text=True,encoding='utf-8',errors='replace')
            if result.returncode: raise RuntimeError(result.stdout[-5000:])
        log=(p/'manuscript.log').read_text(encoding='utf-8',errors='replace')
        warnings=re.findall(r'(?:Overfull[^\n]+|Missing character[^\n]+|[^\n]*undefined[^\n]*)',log)
        (root/'manuscripts'/(stem+'.tex')).write_text(text,encoding='utf-8')
        shutil.copyfile(p/'manuscript.pdf',root/'manuscripts'/(stem+'.pdf'))
        print(stem+': '+('; '.join(warnings) if warnings else 'OK'))
