"""Seal the exact reviewed-to-be IE23 statement boundary before any proof."""
from pathlib import Path
import datetime,hashlib,json,re,subprocess
OUT=Path(__file__).resolve().parent
PROJECT=OUT.parent
REPO=PROJECT.parents[2]
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert not (PROJECT/'Solution.lean').exists()
assert not (PROJECT/'NLA/IE23/Proof.lean').exists()
assert len(re.findall(r'\bsorry\b',(PROJECT/'Challenge.lean').read_text()))==8
assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b',
                     (PROJECT/'NLA/IE23/Definitions.lean').read_text())
checks=json.loads((OUT/'fresh-checks.json').read_text())
assert checks['status']=='PASS' and checks['fresh_commands']==3
for relative,digest in checks['boundary_after'].items():
    assert sha(PROJECT/relative)==digest,relative
reconstruction=json.loads((OUT/'reconstruction.json').read_text())
assert reconstruction['status']=='PASS'
assert reconstruction['script_sha256']==sha(OUT/'reconstruct.py')
source=json.loads((OUT/'source-integrity.json').read_text())
sources={}
for record in source['original_files']:
    assert sha(REPO/record['path'])==record['sha256']
    assert sha(PROJECT/record['snapshot'])==record['sha256']
    sources[record['path']]=record['sha256']
files={}
for p in sorted(PROJECT.rglob('*')):
    relative=p.relative_to(PROJECT)
    if not p.is_file() or any(x in relative.parts for x in ['.lake','.verification','__pycache__']):continue
    if relative.as_posix() in ['reviews/statement-freeze.json','reviews/statement-handoff.md']:continue
    files[relative.as_posix()]=sha(p)
status=subprocess.check_output(['git','status','--porcelain'],cwd=REPO,text=True)
assert status.strip()=='?? linear-systems-and-elimination/IE-23/lean/',status
data={'phase':'statement-only-before-two-independent-reviews',
      'date_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
      'base':source['base'],'branch':'codex/lean-ie23-induced-norm-nonuniqueness',
      'canonical_status':'Solved, unchanged','files':files,'source_files':sources,
      'proof_absent':True,'Challenge_placeholders':8,'fresh_commands':3,
      'definition_kernel_audits':19,'clean_dependency_pins':10,
      'dependency_artifacts':'Read-only pinned private MI22 cache; no old project artifacts; exact paths in fresh-checks.json',
      'local_lake_build_run':False,'Linux_Comparator_run':False,
      'statement_review_approvals':0}
(OUT/'statement-freeze.json').write_text(json.dumps(data,indent=2)+'\n')
print(json.dumps({'status':'FROZEN','files':len(files),'original_sources':len(sources),
                  'freeze_sha256':sha(OUT/'statement-freeze.json'),
                  'mathematical_boundary':{x:files[x] for x in ['NLA/IE23/Definitions.lean','Challenge.lean','NUMERICAL_TARGETS.md','SOURCE_CORRESPONDENCE.md']}}))
