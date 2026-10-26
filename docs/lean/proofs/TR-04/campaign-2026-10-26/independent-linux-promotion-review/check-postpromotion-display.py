#!/usr/bin/env python3
"""Read-only ID/catalog/display binding after the approved TR04 promotion."""
from pathlib import Path
from datetime import datetime,timezone
from collections import Counter
import contextlib,hashlib,io,json,re,subprocess,sys
B=Path(__file__).resolve().parent;REPO=B.parents[5]
HEAD='09cd782576559502787fb536bc1427bf64b7b3e4';OLD='027aaefbadf602ac460d0cf4cae7beed3181d712'
artifacts={}
def sha(p):
    assert p.is_file() and not p.is_symlink(),str(p)
    return hashlib.sha256(p.read_bytes()).hexdigest()
def bind(p,h=None):
    actual=sha(p)
    if h is not None:assert actual==h,str(p)
    artifacts[str(p.relative_to(REPO))]=actual
    return actual
def blob(ref,path):return subprocess.check_output(['git','show',ref+':'+path],cwd=REPO)
def tracked(p):
    bind(p);assert p.read_bytes()==blob(HEAD,str(p.relative_to(REPO)))
sys.path.insert(0,str(REPO/'tools'))
import update_catalog as catalog
import validate_problem_ids as ids
assert ids.ROOT==catalog.ROOT==REPO
assert ids.validate(REPO,'origin/main')==217
assert ids.validate(REPO,OLD)==217
registry=json.loads((REPO/'problem_ids.json').read_text());assert len(registry)==217
tracked(REPO/'problem_ids.json')
assert (REPO/'problem_ids.json').read_bytes()==blob(OLD,'problem_ids.json')
for ident,path in registry.items():
    tracked(REPO/path)
    if ident!='TR-04':assert (REPO/path).read_bytes()==blob(OLD,path)
counts=Counter(catalog.read_problem(REPO/path)['status'] for path in registry.values())
assert sum(counts.values())==217 and counts['Lean verified']==87 and counts['Solved']==31
assert catalog.read_problem(REPO/registry['TR-04'])['status']=='Lean verified'
proposal_path=REPO/'docs/lean/proofs/TR-04/campaign-2026-10-26/promotion-draft/PROMOTION_PROPOSAL.json'
bind(proposal_path,'c352fedca0c34cf23c89e41fdc82cb870ff552b5d50c6fe01a1fc6b5d47a11b0')
proposal=json.loads(proposal_path.read_text())
for rec in proposal['proposed_replacements']:
    p=REPO/rec['destination'];bind(p,rec['proposed_sha256'])
    bind(REPO/rec['proposed_path'],rec['proposed_sha256'])
original=blob(OLD,registry['TR-04']);promoted=(REPO/registry['TR-04']).read_bytes()
assert original.split(b'## Problem statement\n',1)[1]==promoted.split(b'## Problem statement\n',1)[1]

# Execute the unchanged generator with every Path.write_text intercepted into
# memory.  No generator output is written to the repository or package.
captured={};original_write=Path.write_text;old_argv=sys.argv
def capture(path,data,*args,**kwargs):
    p=path.resolve()
    assert p.is_relative_to(REPO) and isinstance(data,str)
    assert p not in captured
    captured[p]=data.encode(kwargs.get('encoding') or 'utf-8')
    return len(data)
log=io.StringIO()
try:
    Path.write_text=capture
    sys.argv=['tools/update_catalog.py','--base-ref','origin/main']
    with contextlib.redirect_stdout(log):catalog.main()
finally:
    Path.write_text=original_write;sys.argv=old_argv
assert set(captured)=={REPO/'README.md',REPO/'CATALOG.md'}|{REPO/c/'README.md' for c in ids.CATEGORIES}
for p,expected in captured.items():
    tracked(p);assert p.read_bytes()==expected,str(p)
    if p.name=='CATALOG.md' or p==REPO/'README.md':
        assert b'31 solved (published or independently audited); 87 solved with Lean verification.' in expected
for p in [REPO/'CATALOG.md',REPO/'tensor-computations/README.md']:
    row=next(x for x in p.read_text().splitlines() if '| [TR-04]' in x)
    assert '**🏆 LEAN VERIFIED**' in row
(B/'postpromotion-catalog-reproduction.log').write_text(log.getvalue());bind(B/'postpromotion-catalog-reproduction.log')
for name in ['tools/validate_problem_ids.py','tools/update_catalog.py','tests/test_problem_ids.py']:
    tracked(REPO/name)
test=subprocess.run([sys.executable,'-m','unittest','discover','-s','tests','-p','test_problem_ids.py','-v'],cwd=REPO,capture_output=True,text=True)
(B/'postpromotion-ID-tests.log').write_text(test.stdout+test.stderr);bind(B/'postpromotion-ID-tests.log')
assert test.returncode==0 and re.search(r'Ran 17 tests\b',test.stderr) and test.stderr.rstrip().endswith('OK')
freeze_path=REPO/'docs/lean/proofs/TR-04/campaign-2026-10-26/CANONICAL_PROMOTION_FREEZE_2026-10-26.json'
bind(freeze_path,'44b5df77ea7ed70c35aac6e87b2001f2b6860a36f58f1156a50d01a3c83374f7')
freeze=json.loads(freeze_path.read_text());assert len(freeze['inputs'])==205
for path,digest in freeze['inputs'].items():bind(REPO/freeze['project']/path,digest)
bind(Path(__file__))
out={'passed':True,'recorded_utc':datetime.now(timezone.utc).isoformat(),'reviewer':'/root/recover_verification',
 'type':'postpromotion_read_only_ID_catalog_display_binding','exact_source_head':HEAD,'original_proof_head':OLD,
 'all217_ID_path_pairs_unchanged':True,'permanent_ID_validator_origin_main_and_original_proof_head_passed':True,
 'all216_other_problem_pages_byte_exact':True,'original_TR04_problem_statement_suffix_exact':True,
 'approved_two_replacements_applied_exactly':True,'status_counts':dict(sorted(counts.items())),
 'all13_catalog_outputs_reproduced_in_memory_byte_exact':len(captured)==13,'catalog_disk_writes_by_check':0,
 'required_ID_tests':17,'required_ID_tests_passed':True,'final205_package_inputs_unchanged':True,
 'final_Linux_Comparator_accepted_by_this_check':False,'new_Lean_execution':False,'proof_source_changes':False,
 'artifact_hashes':artifacts}
q=B/'POSTPROMOTION_DISPLAY.json';assert not q.exists();q.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'passed':True,'sha256':sha(q),'bound_artifacts':len(artifacts),'status_counts':out['status_counts']},indent=2))
