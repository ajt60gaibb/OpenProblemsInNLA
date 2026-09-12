from pathlib import Path
import os,re,subprocess,tempfile
w=Path(__file__).resolve().parents[2]; p=w/'randomized-and-low-rank-approximation/KE-05'
pandoc=os.environ.get('PANDOC','pandoc')
s=(p/'solution.md').read_text()
# The rendering copy expands repository-relative links; the published Markdown stays unchanged.
urlbase='https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/main/'
def link(m):
    label,target=m.groups()
    if '://' in target or target.startswith('#'): return m.group(0)
    target_path=(p/target).resolve().relative_to(w.resolve())
    return '['+label+']('+urlbase+str(target_path)+')'
s=re.sub(r'\[([^\]]+)\]\(([^)]+)\)',link,s)
body=subprocess.run([pandoc,'--from=markdown+tex_math_dollars+raw_tex','--to=latex','--wrap=none'],input=s,text=True,check=True,capture_output=True).stdout
body=body.replace('\\section{KE-05:', '\\section*{KE-05:',1)
body=re.sub(r'(\\subsection\{)',r'\\Needspace{10\\baselineskip}\n\1',body)
body=body.replace('\\[','\\nopagebreak[3]\n\\[')
head=r'''% Standalone manuscript generated from solution.md with Pandoc.
% Compile twice with XeLaTeX.
\documentclass[10pt,a4paper]{article}
\usepackage[margin=24mm,headheight=15pt]{geometry}
\usepackage{fontspec}
\setmainfont{DejaVuSerif.ttf}[BoldFont=DejaVuSerif-Bold.ttf,ItalicFont=DejaVuSerif-Italic.ttf,BoldItalicFont=DejaVuSerif-BoldItalic.ttf]
\setsansfont{DejaVuSans.ttf}[BoldFont=DejaVuSans-Bold.ttf,ItalicFont=DejaVuSans-Oblique.ttf]
\setmonofont{DejaVuSansMono.ttf}
\usepackage{amsmath,amssymb,unicode-math}
\setmathfont{latinmodern-math.otf}
\usepackage{xcolor,microtype,parskip,needspace,fancyhdr}
\usepackage{bookmark,xurl}
\hypersetup{colorlinks=true,urlcolor=blue,linkcolor=blue,pdftitle={KE-05: failure of spectrum-uniform probabilistic interpolation bounds},pdfauthor={George Stepaniants},pdflang={en-GB}}
\urlstyle{same}
\setlength{\emergencystretch}{3em}
\providecommand{\tightlist}{\setlength{\itemsep}{0pt}\setlength{\parskip}{0pt}}
\providecommand{\pandocbounded}[1]{#1}
\setcounter{secnumdepth}{0}
\allowdisplaybreaks[1]
\widowpenalty=10000
\clubpenalty=10000
\pagestyle{fancy}
\fancyhf{}
\fancyhead[L]{\small\sffamily NEGATIVE RESOLUTION / KE-05}
\fancyhead[R]{\small\sffamily 12 September 2026 (UTC)}
\fancyfoot[L]{\parbox[b]{0.9\textwidth}{\fontsize{8}{10}\selectfont Substantial AI assistance; independent automated review is documented separately.}}
\fancyfoot[R]{\footnotesize\thepage}
\begin{document}
'''
tex=head+body+'\n\\end{document}\n'
(p/'solution.tex').write_text(tex)
build=Path(tempfile.mkdtemp(prefix='ke05-solution-build-'))
for i in [1,2]:
    q=subprocess.run(['xelatex','-interaction=nonstopmode','-halt-on-error','-output-directory='+str(build),str(p/'solution.tex')],capture_output=True,text=True)
    (build/f'pass-{i}.log').write_text(q.stdout+q.stderr)
    if q.returncode: print(q.stdout[-10000:]);q.check_returncode()
(p/'solution.pdf').write_bytes((build/'solution.pdf').read_bytes())
log=(build/'solution.log').read_text()
print('\n'.join(line for line in log.splitlines() if any(x in line for x in ['Overfull','Missing character','Output written'])))
