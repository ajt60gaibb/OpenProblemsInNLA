"""Freeze once, or verify, the complete RA08 statement package and original sources."""
from pathlib import Path
import datetime,hashlib,json,subprocess
P=Path(__file__).resolve().parents[1];R=P.parents[2]
OUT=P/'reviews/statement-freeze.json'
def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def git(args):return subprocess.check_output(['git',*args],cwd=R).decode().strip()
if OUT.exists():
    d=json.loads(OUT.read_text())
    for name,digest in d['files'].items():assert sha(P/name)==digest,name
    for name,digest in d['source_files'].items():
        assert sha(R/name)==digest,name
        blob=subprocess.check_output(['git','show',d['base']+':'+name],cwd=R)
        assert hashlib.sha256(blob).hexdigest()==digest,name
        assert git(['rev-parse',d['base']+':'+name])==d['source_git_blobs'][name]
    print('PASS: unchanged',len(d['files']),'frozen project files and',len(d['source_files']),'original sources')
else:
    assert not (P/'Solution.lean').exists() and not (P/'NLA/RA08/Proof.lean').exists()
    sources=json.loads((P/'source-inputs.json').read_text());base=sources['source_commit']
    assert git(['rev-parse','HEAD'])==base
    files={}
    for f in sorted(P.rglob('*')):
        if not f.is_file() or f==OUT:continue
        rel=f.relative_to(P)
        if any(part in {'.lake','.verification','__pycache__'} for part in rel.parts):continue
        assert f.suffix not in {'.olean','.ilean','.pyc'},str(rel)
        files[rel.as_posix()]=sha(f)
    d={'phase':'statement-only-before-two-independent-approvals',
       'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
       'base':base,'branch':git(['branch','--show-current']),
       'canonical_status':'Solved, unchanged','statement_author':'/root/formal_review_standards',
       'proof_route_contributors':['/root/formal_review_standards','/root'],
       'assigned_statement_referees':['/root/solved_statement_inventory','/root'],
       'independent_approvals_present_at_freeze':False,
       'file_count':len(files),'files':files,'source_file_count':len(sources['sources']),
       'source_files':{k:v['sha256'] for k,v in sources['sources'].items()},
       'source_git_blobs':{k:v['git_blob'] for k,v in sources['sources'].items()},
       'boundary':['NLA/RA08/Definitions.lean','Challenge.lean','NUMERICAL_TARGETS.md'],
       'requirements':'No proof implementation before two accepted independent statement approvals. Fourteen intentional Challenge holes are not proofs. Preserve all full original quantifiers, actual definitions, exact numerical target and pins. No replaceable definition holes. Complete proof reviews and actual Linux verification remain pending. Only this exact outer freeze path is excluded from its own file listing.'}
    OUT.write_text(json.dumps(d,indent=2)+'\n')
    print('FROZEN:',len(files),'project files;',len(sources['sources']),'original sources')
print('Freeze SHA256:',sha(OUT))
