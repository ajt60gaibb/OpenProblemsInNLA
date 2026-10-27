#!/usr/bin/env python3
"""Read-only immutable IE22 canonical assembly/preservation review."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess

parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--repo',type=Path,required=True)
parser.add_argument('--output',type=Path,required=True)
parser.add_argument('--extract-project',type=Path)
args=parser.parse_args();ROOT=args.repo.resolve();OUT=args.output.resolve();OUT.mkdir(parents=True,exist_ok=True)
ORIGINAL_PACKAGE='577846438f6cdb80bf237fc190021ddafd7a24a5'
COMMIT='06f31cdd4f76d90c7590b5582b8db4975a0055d8'
SOURCE='353ebcfcbbcfc08184c32f391ecb6068c7d9098f'
BASE='5487945e5a72abd952b0c89915915de8cc9b3e65'
PROBLEM='linear-systems-and-elimination/IE-22/'
PACKAGE=PROBLEM+'lean/'
DOC='docs/lean/proofs/IE-22/campaign-2026-10-23/'
git=lambda *a:subprocess.check_output(['git',*a],cwd=ROOT)
read=lambda c,p:git('show',c+':'+p)
sha=lambda b:hashlib.sha256(b).hexdigest()
obj=lambda p:json.loads(read(COMMIT,p))
paths=lambda c,p:git('ls-tree','-r','--name-only',c,p).decode().splitlines()
checks=[]
def check(name,passed,**detail):checks.append(dict(name=name,passed=bool(passed),**detail))
source_lock=json.loads(read(SOURCE,DOC+'FULL_SOURCE_CHECKPOINT.json'))
copies=[]
for x in source_lock['files']:
    src=x['path'];dest=PACKAGE+src.removeprefix('lean-statements/')
    b=read(SOURCE,src)
    check('reviewed-shared-source-unchanged:'+src,b==read(COMMIT,src)==read(ORIGINAL_PACKAGE,src))
    check('exact-canonical-copy:'+dest,b==read(COMMIT,dest)==read(ORIGINAL_PACKAGE,dest) and sha(b)==x['sha256'])
    copies.append(dict(source=src,destination=dest,sha256=sha(b)))
check('exact-23-source-copies',len(copies)==23)
package_paths=paths(COMMIT,PACKAGE)
initial_paths=paths(ORIGINAL_PACKAGE,PACKAGE)
lean_paths=[p for p in package_paths if p.endswith('.lean')]
check('actual-canonical-lean-set27',len(lean_paths)==27)
for p in lean_paths:check('all-canonical-lean-unchanged-after577:'+p,read(COMMIT,p)==read(ORIGINAL_PACKAGE,p))
package_delta=git('diff','--name-status',ORIGINAL_PACKAGE,COMMIT,'--',PACKAGE).decode().splitlines()
check('only-post577-package-delta-is-old-comparator-text',package_delta==['A\t'+PACKAGE+'original-scaffold/comparator.json.txt'])
pre=obj(DOC+'preproof/INPUT_LOCK.json')
preservation=[]
for x in pre['reviewed_inputs']:
    old=read(BASE,x['path']);frozen=DOC+'preproof/frozen/'+x['path']
    check('all-32-originals-frozen-exact:'+x['path'],old==read(COMMIT,frozen) and sha(old)==x['sha256'] and len(old)==x['bytes'])
    live=read(COMMIT,x['path'])
    archive=None
    if live!=old and x['path'].startswith(PACKAGE):
        archive=PACKAGE+'original-scaffold/'+x['path'].removeprefix(PACKAGE)+'.txt'
        check('changed-scaffold-exact-text-archive:'+x['path'],archive in package_paths and read(COMMIT,archive)==old)
    preservation.append(dict(original=x['path'],sha256=sha(old),frozen=frozen,current_unchanged=live==old,extra_text_archive=archive))
check('exact32original-input-count',len(preservation)==32)
check('canonical-originalREADME-and-Solved-status-unchanged',read(COMMIT,PROBLEM+'README.md')==read(BASE,PROBLEM+'README.md') and b'**Status:** Solved' in read(COMMIT,PROBLEM+'README.md'))
check('added-originalREADME-exact',read(COMMIT,PROBLEM+'ORIGINAL.md')==read(BASE,PROBLEM+'README.md'))
check('registry217pairs-byte-identical',read(COMMIT,'problem_ids.json')==read(BASE,'problem_ids.json') and len(obj('problem_ids.json'))==217)
challenge=read(COMMIT,PACKAGE+'Challenge.lean')
check('canonical-Challenge-exact-approved-bytes',challenge==read(COMMIT,DOC+'preproof/Challenge.lean') and sha(challenge)=='bd20cbb3d4495ff312192ab29fe7722463c8b74861f0a00ae83dd9b98ed4ec79')
names=['NLA.Proofs.IE22.uniform_squared_upper','NLA.Proofs.IE22.near_sharp_unit_row_witness','NLA.Proofs.IE22.target']
cfg=obj(PACKAGE+'comparator.json')
check('exact3-Comparator-names-zero-definition-holes',cfg['theorem_names']==names and cfg['definition_names']==[] and cfg['challenge_module']=='Challenge' and cfg['solution_module']=='Solution')
check('only-standard-three-permitted-axioms',set(cfg['permitted_axioms'])=={'propext','Classical.choice','Quot.sound'})
solution=read(COMMIT,PACKAGE+'Solution.lean').decode()
check('Solution-imports-actual-Final-never-Challenge','import NLA.Proofs.IE22.Final' in solution and 'import Challenge' not in solution)
check('all5-selected-and-historical-export-kernel-assertions',all('#assert_trust kernel '+n in solution for n in names+['IE22.l2Sq_zero','IE22.rowEnergy_empty']))
oldsolution=read(BASE,PACKAGE+'Solution.lean').decode();oldbody=oldsolution[oldsolution.index('namespace IE22'):]
check('two-old-helper-proof-bodies-preserved',oldbody in solution)
check('old-Definitions-byte-preserved',read(COMMIT,PACKAGE+'Definitions.lean')==read(BASE,PACKAGE+'Definitions.lean'))
for p in lean_paths:
    if p!=PACKAGE+'Challenge.lean':check('no-positive-Challenge-import:'+p,not re.search(r'^\s*import\s+.*\bChallenge\b',read(COMMIT,p).decode(),re.M))
identity=read(COMMIT,PACKAGE+'Identity.lean').decode()
check('actual-definitional-live-frozen-identity','NLA.Statements.IE22.Target = NLA.ReviewedStatements.IE22.Target := rfl' in identity)
manifest=obj(PACKAGE+'lake-manifest.json');shared=obj('lean-statements/lake-manifest.json')
check('all-ten-dependency-records-exact-shared-pins',len(manifest['packages'])==10 and manifest['packages']==shared['packages'])
check('official-toolchain-unchanged',read(COMMIT,PACKAGE+'lean-toolchain')==read(BASE,PACKAGE+'lean-toolchain')==b'leanprover/lean4:v4.33.1\n')
meta=obj(PACKAGE+'formalization.yaml')
check('metadata-exact-three-main-results',[x['declaration'] for x in meta['status']['main_results']]==names)
check('metadata-honest-no-complete-or-Linux-promotion',meta['status']['whole_problem_verified'] is False and meta['status']['canonical_status']!='Lean verified' and all('pending' in x['verification_status'] for x in meta['status']['main_results']))
check('metadata-original-math-credit-and-AI-no-endorsement','Matthew J. Colbrook' in json.dumps(meta) and 'no source-author participation or external human endorsement' in json.dumps(meta))
check('metadata-three-axioms-all-main-results',set(meta['status']['axioms'])==set(cfg['permitted_axioms']) and all(set(x['axioms'])==set(cfg['permitted_axioms']) and x['sorry_count']==0 for x in meta['status']['main_results']))
author=obj(DOC+'author-canonical-local/result.json')
check('author-result-clearly-not-Linux','author' in author['scope'] and 'not Linux/Comparator' in author['scope'])
for m,x in author['inputs'].items():check('all27-author-fresh-input-bindings:'+m,sha(read(COMMIT,PACKAGE+x['path']))==x['sha256'])
check('author-snapshots-cover-exact27Lean-input-set',{PACKAGE+x['path'] for x in author['inputs'].values()}==set(lean_paths))
package_hashes={p.removeprefix(PACKAGE):sha(read(COMMIT,p)) for p in package_paths}
if args.extract_project:
    extract=args.extract_project.resolve();extract.mkdir(parents=True,exist_ok=False)
    for p in package_paths:
        dest=extract/p.removeprefix(PACKAGE);dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(read(COMMIT,p))
result=dict(date='2026-10-25',reviewer='/root/inventory',authored_IE22_proof_sources=[],commit=COMMIT,original_package_commit=ORIGINAL_PACKAGE,reviewed_source_commit=SOURCE,published_original_base=BASE,
    verdict='APPROVE exact canonical package assembly and preservation; actual independent kernel/Comparator/Linux acceptance remain separate',
    passed=all(x['passed'] for x in checks),check_count=len(checks),checks=checks,copy_count=len(copies),copies=copies,
    canonical_package_input_count=len(package_paths),canonical_lean_input_count=len(lean_paths),all_canonical_package_hashes=package_hashes,
    original32preservation=preservation,post577package_delta=package_delta,author_result_sha256=sha(read(COMMIT,DOC+'author-canonical-local/result.json')),
    scope='Source-copy, exact boundary, preservation, metadata and provenance audit. Existing author compiler evidence inspected as author evidence only; no new kernel/CI replay.',
    auditor_sha256=sha(Path(__file__).read_bytes()))
(OUT/'PACKAGE_REVIEW_INVENTORY.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:result[k] for k in ['passed','check_count','canonical_package_input_count','canonical_lean_input_count','copy_count','verdict']},indent=2))
if not result['passed']:
    print(json.dumps([x for x in checks if not x['passed']],indent=2));raise SystemExit(1)
