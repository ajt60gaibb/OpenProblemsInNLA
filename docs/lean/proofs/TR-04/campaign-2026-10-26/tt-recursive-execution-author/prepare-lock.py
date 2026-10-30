#!/usr/bin/env python3
"""Freeze the actual recursive execution closure and explicit author declarations."""
from pathlib import Path
import datetime,hashlib,json,re
HERE=Path(__file__).resolve().parent
REPO=HERE.parents[5];LIVE=REPO/'lean-statements'
h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def rec(path):
 p=REPO/path
 return dict(path=str(path),sha256=h(p),bytes=p.stat().st_size)
modules=['MachineTTRecursiveState','TTRecursiveDimensions','MachineTTStageMetadata','MachineTTStageForward','TTRecursiveBudget','MachineTTStageChildSVD','MachineTTRecursiveResult','MachineTTStageReverse','MachineTTRecursiveBase','MachineTTRecursiveExecution','MachineTTRecursiveChild']
authored=[rec('lean-statements/NLA/Proofs/TR04/'+n+'.lean') for n in modules]
decls=[]
for n in modules:
 s=(LIVE/'NLA/Proofs/TR04'/f'{n}.lean').read_text()
 ns=re.search(r'^namespace\s+(\S+)',s,re.M).group(1)
 decls += [ns+'.'+x for x in re.findall(r'^\s*(?:def|theorem|structure)\s+([\w.]+)',s,re.M)]
seen=set();closure=[]
def visit(mod):
 if mod in seen:return
 seen.add(mod);p=LIVE/(mod.replace('.','/')+'.lean')
 for dep in re.findall(r'^import\s+(\S+)\s*$',p.read_text(),re.M):
  if dep.startswith(('NLA.','Reviewed.')):visit(dep)
 closure.append(rec(p.relative_to(REPO)))
targets=['NLA.Proofs.TR04.MachineTTRecursiveChild']
for t in targets:visit(t)
prior=[HERE.parent/'RECURSIVE_STAGE_SUPPORT_FREEZE_2026-10-26.json',HERE.parent/'RECURSIVE_EXECUTION_CORE_FREEZE_2026-10-26.json',HERE.parent/'tt-reverse-author/source-lock.json',HERE.parent/'tt-forward-author/source-lock.json',HERE.parent/'child-initialization-author/source-lock.json',HERE.parent/'tt-child-svd-loop-author/source-lock.json',HERE.parent/'CHILD_SVD_LOOP_STATE_FREEZE_2026-10-26.json']
original=json.loads((HERE.parent.parent/'campaign-2026-10-23/input-lock.json').read_text())['records'];assert len(original)==25
boundary=json.loads((HERE.parent/'tt-reverse-author/source-lock.json').read_text())['unchanged_boundary_and_pins']
lock=dict(author='/root/recover_geometry',frozen_at_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),scope='Actual shared241 full recursive tensor execution plus every legal child237 SVD response, saved-parent metadata/frame restore and actual stored Completion/time/charge; author kernel replay only, no full Target/Linux CI/Comparator claim',targets=targets,authored_sources=authored,authored_declarations=decls,project_closure=closure,unchanged_boundary_and_pins=boundary,reviewed_original_inputs=original,prior_frozen_evidence=[rec(p.relative_to(REPO)) for p in prior])
(HERE/'source-lock.json').write_text(json.dumps(lock,indent=2)+'\n')
asserts='\n'.join('#assert_trust kernel '+d+'\n#print axioms '+d for d in decls)
(HERE/'declaration-assertions.lean').write_text(asserts+'\n')
print('source-lock',h(HERE/'source-lock.json'),'authored',len(authored),'closure',len(closure),'explicit_declarations',len(decls))
