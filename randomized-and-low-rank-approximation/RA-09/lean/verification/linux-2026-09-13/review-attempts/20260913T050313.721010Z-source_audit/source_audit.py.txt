"""Independent RA-09 committed-source/context audit before remote acceptance.

No Lean execution, cache operation, network operation, or Git mutation.
Original candidate files are hash-bound in place and as Git objects; they are
not redundantly copied into this operational evidence directory.
"""
from pathlib import Path
import ast,hashlib,json,re,subprocess

O=Path(__file__).resolve().parent
C=json.loads((O/'context.json').read_text())
W=Path(C['worktree']).resolve()
P=W/C['project']
COMMIT=C['commit']
BASE='5830ed4fb06da0659414a3deb2a40ad327aca052'
def sha(b):return hashlib.sha256(b).hexdigest()
def git(*a):return subprocess.check_output(['git',*a],cwd=W)
def save(n,d):(O/n).write_text(json.dumps(d,indent=2)+'\n')
def retain(n):
    b=git('show',COMMIT+':'+n)
    assert b==(W/n).read_bytes(),n
    p=O/'source'/n;p.parent.mkdir(parents=True,exist_ok=True)
    if p.exists():assert p.read_bytes()==b,n
    else:p.write_bytes(b)
    return b

assert git('rev-parse','HEAD').decode().strip()==COMMIT
tree=git('ls-tree','-r','-z',COMMIT,'--',C['project'])
inputs={}
for entry in tree.split(b'\0'):
    if not entry:continue
    header,path=entry.split(b'\t',1)
    mode,kind,blob=header.decode().split()
    assert kind=='blob' and mode in ['100644','100755']
    name=path.decode();rel=str(Path(name).relative_to(C['project']))
    data=git('cat-file','blob',blob)
    assert (W/name).read_bytes()==data,name
    inputs[rel]={'sha256':sha(data),'bytes':len(data),'git_blob':blob,'mode':mode}
assert len(inputs)==C['candidate_project_inputs']==524
(O/'source').mkdir(exist_ok=True)
(O/'source/git-project-tree.txt').write_bytes(git('ls-tree','-r',COMMIT,'--',C['project']))
commit=git('cat-file','commit',COMMIT)
(O/'source/git-commit.txt').write_bytes(commit)
assert re.search(rb'^author George Stepaniants <> ',commit,re.M)
assert re.search(rb'^committer George Stepaniants <> ',commit,re.M)

proof=json.loads((P/'verification/proof-freeze.json').read_text())
statement=json.loads((P/'reviews/statement-freeze.json').read_text())
assert inputs['verification/proof-freeze.json']['sha256']=='533f5c328cdaf8c1f23f238f8c71b7b4b2fdabb2f532d58a398d4ab2434ccf7e'
assert inputs['reviews/statement-freeze.json']['sha256']=='c144b68990fca06c554790b25bfaef7544c0a8baf532e5b38365fe74ee9c87ed'
archive={'README.md':'verification/pre-candidate-README.md'}
for freeze,count in [(proof,361),(statement,31)]:
    assert freeze['base']==BASE and len(freeze['files'])==count
    for n,h in freeze['files'].items():
        assert inputs[archive.get(n,n)]['sha256']==h,n
assert proof['source_files']==statement['source_files']
assert proof['source_git_blobs']==statement['source_git_blobs']
assert len(proof['source_files'])==17
originals={}
for n,h in proof['source_files'].items():
    b=retain(n)
    assert b==git('show',BASE+':'+n) and sha(b)==h,n
    blob=git('rev-parse',BASE+':'+n).decode().strip()
    assert blob==statement['source_git_blobs'][n]
    originals[n]={'sha256':h,'bytes':len(b),'git_blob':blob}

installation=json.loads((P/'verification/linux-candidate-2026-09-13/INSTALLATION.json').read_text())
assert len(installation['baseline'])==499
for n,r in installation['baseline'].items():
    target=archive.get(n,n)
    assert inputs[target]['sha256']==r['sha256'] and inputs[target]['bytes']==r['bytes'],n
for n,h in installation['wrapper_files'].items():assert inputs[n]['sha256']==h,n
def manifest(n,complete=True):
    f=P/n;m=json.loads(f.read_text());bound=set()
    for rel,r in m['files'].items():
        target=(f.parent/rel).resolve()
        assert target.is_relative_to(P),rel
        t=str(target.relative_to(P));assert t in inputs,t
        h=r['sha256'] if isinstance(r,dict) else r
        assert inputs[t]['sha256']==h,(n,rel)
        if isinstance(r,dict) and 'bytes' in r:assert inputs[t]['bytes']==r['bytes']
        if not rel.startswith('../'):bound.add(rel)
    if complete:
        prefix=str(f.parent.relative_to(P))+'/'
        actual={r[len(prefix):] for r in inputs if r.startswith(prefix) and r!=n}
        assert actual==bound,(n,actual-bound,bound-actual)
    if 'file_count' in m:assert m['file_count']==len(m['files'])
    return {'sha256':inputs[n]['sha256'],'bound_files':len(m['files']),'complete_in_its_declared_phase_scope':True}

nested={}
for n in inputs:
    if Path(n).name=='EVIDENCE-MANIFEST.json':nested[n]=manifest(n)
assert len(nested)==13
root=json.loads((P/'verification/root-candidate-2026-09-13/ROOT-CHECKS.json').read_text())
assert len(root['prior_inputs'])==root['prior_input_count']==520
for n,h in root['prior_inputs'].items():
    assert inputs[n]['sha256']==h,n
rootfiles={n for n in inputs if n.startswith('verification/root-candidate-2026-09-13/')}
assert len(rootfiles)==4 and not set(root['prior_inputs'])&rootfiles
assert set(root['prior_inputs'])|rootfiles==set(inputs)
assert inputs['verification/linux-candidate-2026-09-13/INSTALLATION.json']['sha256']==root['installation_sha256']
packreport='reviews/candidate-packaging-referee-2026-09-13.md'
assert inputs[packreport]['sha256']==root['independent_packaging_report_sha256']=='9d74a02767975969022abd594e813bfde0c0c5b2a26f28f79623cffecde01d47'
for n,r in root['complete_package_inventories'].items():
    assert inputs[n]['sha256']==r['sha256'] and nested[n]['bound_files']==r['bound_files']
assert root['canonical_status']=='Solved, unchanged'
gate=json.loads((P/'verification/final-review-acceptance.json').read_text())
assert inputs['verification/final-review-acceptance.json']['sha256']==root['final_review_gate_sha256']=='ed2eef518099d23090e21786b626a111d511b32fea12e7193442273e2d980132'
assert len(gate['reports'])==2
for r in gate['reports']:
    assert inputs[r['report']]['sha256']==r['sha256']
    assert inputs[r['evidence']['path']]['sha256']==r['evidence']['sha256']
    assert nested[r['evidence']['path']]['bound_files']==r['evidence']['bound_files']
    assert (r['successful_direct_source_commands'],r['actual_standard_three_reports'])==((18,66) if r['report']=='reviews/final-referee-1.md' else (19,50))
    assert r['mathematical_revision_requested'] is False
names=['frobenius_semantics','frobenius_orthogonal_invariance','orderedSpectral_exists',
    'orderedSpectral_semantics','functionalCalculus_spectral','truncation_semantics',
    'trace_deficit_reduction','admissible_scalar_consequences','scalar_branch_certificates',
    'ordered_scalar_certificate','harmonic_constraint','overlap_semantics','overlap_error_expansions',
    'zero_column_average','positive_tail_transfer','zero_tail_closure','concaveFrobeniusTransferConjecture']
config=json.loads((P/'comparator.json').read_text())
assert config['theorem_names']==installation['exports']==['NLA.RA09.'+n for n in names]
assert config['definition_names']==[] and config['permitted_axioms']==['propext','Classical.choice','Quot.sound']
def headers(file):
    text=(P/file).read_text()
    return {m.group(1):' '.join(text[m.end():text.index(':=',m.end())].split())
      for m in re.finditer(r'^theorem\s+(\w+)\s+',text,re.M)}
assert headers('Challenge.lean')==headers('Solution.lean')
assert list(headers('Solution.lean'))==names
scan={}
for f in sorted((P/'NLA/RA09').glob('*.lean'))+[P/'Solution.lean']:
    code=re.sub(r'/\-.*?\-/','',f.read_text(),flags=re.S)
    code=re.sub(r'--[^\n]*','',code)
    assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe)\b',code),f
    assert not re.search(r'^import\s+Challenge\b',code,re.M),f
    assertions=re.findall(r'^#assert_trust kernel\s+(\S+)',code,re.M)
    prints=re.findall(r'^#print axioms\s+(\S+)',code,re.M)
    assert assertions==prints,f
    n=str(f.relative_to(P));scan[n]={'sha256':inputs[n]['sha256'],'kernel_assertions':assertions}
assert sum(len(r['kernel_assertions']) for r in scan.values())==49
for n in ['NLA/RA09/Proof.lean','Solution.lean']:
    assert 'set_option leancert.trust "kernel"' in (P/n).read_text()
assert '**Status:** Solved' in (P.parent/'README.md').read_text()
for n in ['README.md','formalization.yaml']:
    text=(P/n).read_text()
    assert 'George Stepaniants' in text and 'California Institute of Technology' in text
    assert 'Department of Computing and Mathematical Sciences' in text
    assert not re.search(r'[A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\.[A-Za-z]{2,}',text)
lock_bytes=retain('tools/lean/source-lock.json');lock=json.loads(lock_bytes)
assert lock['commit']=='8d1b0c0545a77b40245e84705aa7d273e6c81e62'
assert lock['lean_toolchain']=='leanprover/lean4:v4.33.1'
assert len(lock['files'])==58
shared=Path('/tmp/nla-lean-formalization/fetched-tool-source-check')
for item in lock['files']:
    data=(shared/item['destination']).read_bytes()
    assert len(data)==item['bytes'] and sha(data)==item['sha256']
    t=O/'source/forsythe'/item['destination'];t.parent.mkdir(parents=True,exist_ok=True)
    if t.exists():assert t.read_bytes()==data
    else:t.write_bytes(data)
harness=retain('tools/lean/harness.py')
node=next(n for n in ast.parse(harness).body if isinstance(n,ast.FunctionDef) and n.name=='ci_probe_source')
ns={'Path':Path,'HarnessError':RuntimeError}
exec(compile(ast.Module(body=[node],type_ignores=[]),'reviewed_ci_probe_source','exec'),ns)
probe=ns['ci_probe_source'](shared).encode()
(O/'source/sandbox_probe_ci.py').write_bytes(probe)
infrastructure={}
for n in ['tools/lean/harness.py','tools/lean/source-lock.json','tools/lean/bootstrap.sh','tools/lean/selftest.sh',
          'tools/lean/verify.sh','tools/lean/projects.py','tools/lean/validate_manifest.py',
          '.github/workflows/lean-verification.yml','docs/lean/schema/v0.4.schema.json','problem_ids.json','AGENTS.md']:
    b=retain(n);assert b==git('show',BASE+':'+n)
    infrastructure[n]={'sha256':sha(b),'bytes':len(b)}
for n in ['tools/lean/harness.py','tools/lean/source-lock.json','tools/lean/bootstrap.sh','tools/lean/selftest.sh','tools/lean/verify.sh']:
    assert (W/n).read_bytes()==git('show','214c142d6bfe0f0c338808f188062acbbad0fb19:'+n)
assert len(json.loads((W/'problem_ids.json').read_text()))==217
assert not git('diff','--name-only') and not git('diff','--cached','--name-only')
save('source-binding.json',{'result':'PASS committed source and review binding; remote acceptance still required',
 'candidate':COMMIT,'base':BASE,'candidate_inputs':inputs,'candidate_input_count':524,'proof_inputs':361,'statement_inputs':31,
 'original_sources':originals,'archive_mapping':archive,'preinstallation_inputs_preserved':499,
 'root_entry_inputs':520,'root_acceptance_inputs':4,'all_candidate_inputs_accounted_once':True,
 'complete_nested_manifests':nested,'accepted_mathematical_reviews':gate['reports'],'config':config,
 'source_trust_scan':scan,'embedded_kernel_assertions':49,
 'final_review_count_scope':'49 assertions are embedded in the candidate; final referee 1 independently reported 66 with 17 extra export checks and final referee 2 50 with one literal consumer.',
 'material_LeanCert_scope':'Pure exact scalar and finite matrix reasoning; actual LeanCert kernel trust/dependency assertions. No interval certificate, numerical oracle or artificial numerical computation.',
 'repository_infrastructure':infrastructure,'source_lock_sha256':sha(lock_bytes),'locked_checker_sources':58,
 'derived_ci_probe_sha256':sha(probe),'proof_coauthors':['/root/formal_review_standards','/root/solved_statement_inventory','/root/leancert_examples','/root'],
 'operational_reviewer':C['role'],'actual_remote_success_claimed':False})
print(json.dumps({'result':'PASS committed source/context binding only','candidate_inputs':524,'nested_manifests':13,
 'exports':17,'embedded_kernel_assertions':49,'locked_sources':58,'remote_acceptance':'pending'}))
