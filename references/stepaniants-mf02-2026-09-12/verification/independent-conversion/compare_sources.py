#!/usr/bin/env python3
"""Read-only independent source conversion comparison for frozen MF-02."""
from pathlib import Path
import difflib
import hashlib
import json
import re

HERE=Path(__file__).resolve().parent
WORKTREE=Path('/tmp/nla-mf02-worktree')
DOC=WORKTREE/'matrix-functions-and-stability/MF-02'
REVIEW=HERE.parent/'independent-review'

def sha(b):
    return hashlib.sha256(b).hexdigest()

def require(test, message):
    if not test:
        raise RuntimeError(message)

def core(s):
    return s[s.index('## 1. Exact target and result'):s.index('## 6.')]

def remove_layout(s):
    return re.sub(r'(?m)^\\Needspace\{12\\baselineskip\}\n\n','',s)

def formulas(s):
    pattern=r'\\\((.*?)\\\)|\\\[(.*?)\\\]|\$\$(.*?)\$\$|(?<!\\)\$(.*?)(?<!\\)\$'
    result=[]
    for m in re.finditer(pattern,s,re.S):
        item=next(x for x in m.groups() if x is not None)
        result.append(re.sub(r'\s+','',item))
    return result

def prose(s, kind):
    # Replace math by ordered placeholders before stripping presentation.
    i=0
    def repl(match):
        nonlocal i
        result=f'MATHPLACEHOLDER{i}'
        i+=1
        return result
    s=re.sub(r'\\\(.*?\\\)|\\\[.*?\\\]',repl,s,flags=re.S)
    s=remove_layout(s)
    if kind=='md':
        s=re.sub(r'(?m)^## +','',s)
        s=s.replace('**','')
        s=re.sub(r'\[([^\]]+)\]\([^)]*\)',r'\1',s)
    else:
        s=re.sub(r'\\subsection\{([^{}]*)\}',r'\1',s,flags=re.S)
        s=re.sub(r'\\label\{[^{}]*\}','',s)
        s=re.sub(r'\\textbf\{([^{}]*)\}',r'\1',s,flags=re.S)
        s=re.sub(r'\\href\{[^{}]*\}\{([^{}]*)\}',r'\1',s,flags=re.S)
    return re.sub(r'\s+',' ',s).strip()

def main():
    frozen=json.loads((HERE.parent/'frozen-artifacts.json').read_text())
    artifact_checks={}
    for name,record in frozen['artifacts'].items():
        b=(WORKTREE/name).read_bytes()
        current={'bytes':len(b),'sha256':sha(b)}
        require(current==record, f'Artifact differs from freeze: {name}')
        artifact_checks[name]=current
    original=(REVIEW/'reviewed-candidate.md').read_text()
    original_target=(REVIEW/'canonical-target.md').read_text()
    md=(DOC/'solution.md').read_text()
    tex=(DOC/'solution.tex').read_text()
    readme=(DOC/'README.md').read_text()
    origcore=core(original)
    pubcore=remove_layout(core(md))
    pattern=r'This theorem gives a constant-factor asymptotic comparison\..*?(?=\n\n)'
    old_scope=re.search(pattern,origcore,re.S).group()
    new_scope=re.search(pattern,pubcore,re.S).group()
    require(pubcore.replace(new_scope,old_scope)==origcore,
            'Mathematical prose differs beyond the one recorded scope paragraph')
    tf=tex[tex.index(r'\subsection{1. Exact target and result}'):tex.index(r'\subsection{6. Attribution, scope, and')]
    require(formulas(origcore)==formulas(pubcore)==formulas(tf), 'Core mathematical expressions differ')
    require(prose(pubcore,'md')==prose(tf,'tex'), 'Core prose differs after presentation normalization')
    require(formulas(md)==formulas(tex), 'Whole-manuscript mathematical expressions differ')
    marker='## Context and notation'
    require(original_target[original_target.index(marker):]==readme[readme.index(marker):],
            'Original target/history suffix differs')
    canonical_tex=(DOC/'problem.tex').read_text()
    require(formulas(readme)==formulas(canonical_tex), 'Canonical README/TeX mathematical expressions differ')
    attribution_md=md[md.index('## 6. Attribution, scope, and verification'):md.index('### References')]
    attribution_tex=tex[tex.index(r'\subsection{6. Attribution, scope, and'):tex.index(r'\subsubsection{References}')]
    require(prose(attribution_md,'md')==prose(attribution_tex,'tex'), 'Attribution prose differs between Markdown and TeX')
    for name in ['solution.md','solution.tex','README.md','problem.tex']:
        s=(DOC/name).read_text()
        require(not re.search(r'[A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\.[A-Za-z]{2,}',s),
                'Email address appears in '+name)
    archived=WORKTREE/'references/stepaniants-mf02-2026-09-12/verification'
    for name in ['MF-02-independent-review.md','reviewed-candidate.md','exact_algebra_check.py','exact-algebra-output.json']:
        require((archived/'independent-review'/name).read_bytes()==(REVIEW/name).read_bytes(),
                'Archived independent review item changed: '+name)
    source_review=HERE.parent/'source-review/REVIEW.md'
    require((archived/'source-review/REVIEW.md').read_bytes()==source_review.read_bytes(),
            'Archived source review changed')
    result={
      'verdict':'PASS',
      'reviewed_original_sha256':sha(original.encode()),
      'original_core':{'bytes':len(origcore.encode()),'sha256':sha(origcore.encode())},
      'published_core_excluding_five_layout_directives':{'bytes':len(pubcore.encode()),'sha256':sha(pubcore.encode())},
      'changed_scope_paragraph':{'before':old_scope,'after':new_scope},
      'all_other_core_bytes_identical':True,
      'ordered_core_formula_count':len(formulas(origcore)),
      'ordered_whole_manuscript_formula_count':len(formulas(md)),
      'core_prose_markdown_tex_equivalent':True,
      'attribution_prose_markdown_tex_equivalent':True,
      'target_history_suffix_byte_identical':True,
      'ordered_canonical_formula_count':len(formulas(readme)),
      'canonical_formulas_match_tex':True,
      'source_files_have_no_email':True,
      'archived_reviews_and_candidate_unchanged':True,
      'source_review_sha256':sha(source_review.read_bytes()),
      'artifacts':artifact_checks,
      'limitations':'Source conversion and scope check only; PDF visual QA is owned by coordinating agent.'
    }
    (HERE/'comparison.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':
    main()
