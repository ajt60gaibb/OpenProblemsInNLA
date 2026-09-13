"""Independent final referee inventory, source, and actual-output audit.
No project mathematics or candidate metadata is modified.
"""
from pathlib import Path
import datetime,hashlib,json,re,subprocess
E=Path(__file__).resolve().parent; P=E.parents[1]; W=P.parents[2]
D=Path('/tmp/nla-lean-mi22-worktree/matrix-inequalities-and-norms/MI-22/lean/.lake/packages')
S=Path('/tmp/nla-lean-formalization/standards')
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
f=json.loads((P/'verification/proof-freeze.json').read_text()); s=json.loads((P/'reviews/statement-freeze.json').read_text())
for data in (f,s):
    for n,h in data['files'].items(): assert sha(P/n)==h,n
    for n,h in data['source_files'].items():
        b=subprocess.check_output(['git','show',data['base']+':'+n],cwd=W)
        assert hashlib.sha256(b).hexdigest()==h and (W/n).read_bytes()==b,n
        assert subprocess.check_output(['git','rev-parse',data['base']+':'+n],cwd=W).decode().strip()==data['source_git_blobs'][n]
assert len(f['files'])==361 and len(s['files'])==31
assert f['source_files']==s['source_files'] and len(f['source_files'])==17

def inventory(rel):
    mf=P/rel; data=json.loads(mf.read_text()); rows=data['files']
    for n,v in rows.items():
        q=mf.parent/n; h=v if isinstance(v,str) else v['sha256']
        assert sha(q)==h,(rel,n)
        if isinstance(v,dict) and 'bytes' in v:assert q.stat().st_size==v['bytes'],(rel,n)
    actual={str(q.relative_to(mf.parent)) for q in mf.parent.rglob('*') if q.is_file() and q!=mf}
    internal={n for n in rows if not n.startswith('../')}
    assert actual==internal,(rel,actual-internal,internal-actual)
    return {'path':rel,'sha256':sha(mf),'bound_files':len(rows),'internal_files':len(internal),
            'complete_internal_inventory':True,'nested_manifest_names_included':[n for n in rows if 'manifest' in n.lower()],
            'only_exact_outer_manifest_excluded':True}
invs=[inventory('verification/'+x+'-development/EVIDENCE-MANIFEST.json') for x in
      ['frobenius','scalar','harmonic','zero-column','zero-tail']]
for x in ['1','2']:invs.append(inventory('reviews/statement-referee-'+x+'-evidence/EVIDENCE-MANIFEST.json'))
start=json.loads((P/'verification/proof-start.json').read_text())
assert start['proof_absent_at_gate'] and len(start['reports'])==2
for r in start['reports']:
    assert sha(P/r['report'])==r['sha256']
    assert sha(P/r['complete_evidence_manifest'])==r['evidence_sha256']

config=json.loads((P/'comparator.json').read_text());names=config['theorem_names']
assert len(names)==17 and config['definition_names']==[]
assert set(config['permitted_axioms'])=={'propext','Classical.choice','Quot.sound'}
headers=lambda text:dict(re.findall(r'^theorem (\w+)(.*?):= by',text,re.M|re.S))
assert headers((P/'Challenge.lean').read_text())==headers((P/'Solution.lean').read_text())
assert ['NLA.RA09.'+n for n in headers((P/'Challenge.lean').read_text())]==names
real=[*sorted((P/'NLA/RA09').glob('*.lean')),P/'Solution.lean']
for q in real:
    src=q.read_text()
    assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe|run_tac)\b',src),q
    assert not re.search(r'^import\s+(Challenge|reviews|verification)\b',src,re.M),q
    assert not re.search(r'set_option\s+leancert.trust\s+"(?!kernel)',src),q
reference=(E/'Reference.lean').read_text().replace('namespace NLA.RA09.FinalReferee1Reference\n','namespace NLA.RA09\n').replace('end NLA.RA09.FinalReferee1Reference\n','end NLA.RA09\n')
assert reference==(P/'Challenge.lean').read_text()
record=json.loads((E/'execution.json').read_text())
assert len(record['commands'])==18 and all(c['exit_code']==0 for c in record['commands'])
assert record['pins_before']==record['pins_after'] and record['frozen_before']==record['frozen_after']
closures=[]; warning_counts={}
for c in record['commands']:
    log=E/c['log']; assert sha(log)==c['log_sha256']
    assert sha(P/c['source'])==c['sha256']
    out=log.read_text();warning_counts[c['source']]=out.count('warning:')
    if c['source'].endswith('/Reference.lean'):assert out.count('warning: declaration uses `sorry`')==17 and out.count('warning:')==17
    else:assert 'warning:' not in out and 'error:' not in out
    for name,axs in re.findall(r"'([^']+)' depends on axioms:\s*\[(.*?)\]",out,re.S):
        ax=[a.strip() for a in axs.split(',') if a.strip()]
        assert set(ax)<= {'propext','Classical.choice','Quot.sound'}
        closures.append({'name':name,'axioms':ax,'log':c['log']})
assert len(closures)==66,len(closures)
log=(E/'reviews-final-referee-1-evidence-Inspect.log').read_text()
type_names=re.findall(r'^EXACT_ELABORATED_SIGNATURE (\S+) = (\S+)$',log,re.M)
assert [x[0] for x in type_names]==names and len(type_names)==17
counts={a:{'project_declarations':int(b),'material_bridges':int(c)} for a,b,c in re.findall(r'^INDEPENDENT_COUNTS (\w+): project=(\d+), material=(\d+)$',log,re.M)}
assert counts=={'FINAL':{'project_declarations':115,'material_bridges':40},'ALL':{'project_declarations':139,'material_bridges':49}},counts
assert 'Matrix.frobeniusNormedAddCommGroup' in log and '@cfc.' in log and '@Matrix.instPreOrder.' in log
assert 'NLA.RA09.functionalCalculus._proof_2' in log
assert 'ACTUAL_EDGE FINAL NLA.RA09.zero_tail_closure_proved:' in log
assert 'ACTUAL_EDGE FINAL NLA.RA09.positive_tail_transfer_proved:' in log
actual_ax=re.findall(r'^ACTUAL_AXIOMS (FINAL|ALL) ([^:]+): \[(.*?)\]',log,re.M|re.S)
# Multiline pretty-printing can wrap a list, hence the explicit closing bracket.
assert len(actual_ax)==254,len(actual_ax)
for mode,name,axs in actual_ax:
    assert 'FinalReferee1Reference' not in name
    assert set(a.strip() for a in axs.split(',') if a.strip()) <= {'propext','Classical.choice','Quot.sound'}

api_paths=['mathlib/Mathlib/Analysis/Matrix/Normed.lean','mathlib/Mathlib/Analysis/Matrix/Order.lean',
'mathlib/Mathlib/LinearAlgebra/Matrix/PosDef.lean','mathlib/Mathlib/LinearAlgebra/Matrix/Trace.lean',
'mathlib/Mathlib/Analysis/Matrix/Spectrum.lean','mathlib/Mathlib/Analysis/Matrix/HermitianFunctionalCalculus.lean',
'mathlib/Mathlib/Analysis/Convex/Function.lean','mathlib/Mathlib/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Unital.lean',
'mathlib/Mathlib/LinearAlgebra/UnitaryGroup.lean','mathlib/Mathlib/Order/Interval/Finset/Fin.lean',
'leancert/LeanCert/Tactic/Verification.lean']
pins={r['name']:r['rev'] for r in record['pins_before']}; api={}
for name in api_paths:
    pkg,rel=name.split('/',1);q=D/pkg/rel
    b=subprocess.check_output(['git','show',pins[pkg]+':'+rel],cwd=D/pkg)
    assert b==q.read_bytes()
    api[name]={'sha256':sha(q),'bytes':len(b),'commit':pins[pkg],
      'git_blob':subprocess.check_output(['git','rev-parse',pins[pkg]+':'+rel],cwd=D/pkg).decode().strip(),
      'scope':'Relevant genuine definition and primary API sections inspected; not a review of every library proof.'}
tree=json.loads((S/'TauCetiProject_TauCetiReview-tree.json').read_text())
assert tree['sha']=='afb424eda89e8ac96d9eb69f6a88972055a4cd1b'
rubrics={}
for n in ['correctness','scope','proof-quality','reuse','generality','api-design','naming','placement','documentation','attribution']:
    rel='rubrics/'+n+'.md';b=(S/'sources/TauCetiProject/TauCetiReview'/rel).read_bytes()
    blob=next(e['sha'] for e in tree['tree'] if e['path']==rel)
    assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==blob
    rubrics[n]={'path':rel,'sha256':hashlib.sha256(b).hexdigest(),'git_blob':blob}
# Reuse searches are retained verbatim and do not assert exhaustive Mathlib novelty.
queries=[['rg','-n','frobenius.*unitary|unitary.*frobenius|frobenius.*mul|trace.*PosSemidef|trace.*posSemidef|harmonic|subhomogeneous|transfer.*frobenius|frobenius.*transfer','Mathlib/Analysis/Matrix','Mathlib/LinearAlgebra/Matrix','Mathlib/Analysis/Convex']]
searches=[]
for i,cmd in enumerate(queries):
    run=subprocess.run(cmd,cwd=D/'mathlib',capture_output=True);out=E/f'reuse-search-{i+1}.log';out.write_bytes(run.stdout+run.stderr)
    assert run.returncode in (0,1)
    searches.append({'command':cmd,'exit_code':run.returncode,'log':out.name,'sha256':sha(out)})
check=subprocess.run(['python3','tools/validate_problem_ids.py','--base-ref',f['base']],cwd=W,capture_output=True)
(E/'permanent-ids.log').write_bytes(check.stdout+check.stderr);assert check.returncode==0
assert not subprocess.check_output(['git','diff','--name-only'],cwd=W)
assert '**Status:** Solved' in (P.parent/'README.md').read_text()
result={'reviewer':'/root/ra09_final_referee1','role':'Independent final mathematical referee 1; AI agent, no statement/proof contribution',
'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'verdict':'PASS_LOCAL_MATHEMATICAL_REVIEW',
'proof_freeze':{'sha256':sha(P/'verification/proof-freeze.json'),'bound_project':len(f['files']),'bound_original_Git':len(f['source_files'])},
'statement_freeze':{'sha256':sha(P/'reviews/statement-freeze.json'),'bound_project':len(s['files'])},
'proof_start_sha256':sha(P/'verification/proof-start.json'),'reviewed_math_files':{str(q.relative_to(P)):sha(q) for q in real},
'completion_report_sha256':sha(P/'reviews/proof-completion.md'),'complete_preserved_inventories':invs,
'exact_literal_signatures':names,'exact_elaborated_signature_comparisons':len(type_names),
'fresh_commands':18,'failed_Lean_commands':0,'standard_three_reports':len(closures),'standard_three_rows':closures,
'actual_project_closure_counts':counts,'actual_transitive_project_axiom_rows':len(actual_ax),
'no_Challenge_reference_or_review_in_implementation':True,'primary_APIs':api,
'Tau_Ceti_revision':tree['sha'],'ten_rubrics_read_and_hash_verified':rubrics,
'local_review_protocol_sha256':sha(W/'docs/lean/REVIEW.md'),'reuse_searches':searches,
'permanent_ids':{'count':len(json.loads((W/'problem_ids.json').read_text())),'validator_exit_code':check.returncode,'log_sha256':sha(E/'permanent-ids.log')},
'comment_only_finding':{'path':'NLA/RA09/OrderedExistence.lean','text':'Mathematical counterexample: Matthew J. Colbrook.','classification':'Nonblocking copied header typo; theorem is affirmative. Frozen source preserved; no mathematical correction requested.'},
'platform_scope':record['scope'],'Linux_Comparator_default_kernel_controls':'not run; separate required operational gate',
'metadata_scope':'Historical statement-stage wrappers remain frozen; truthful candidate README and v0.4 manifest still required after final approvals.',
'canonical_status':'Solved, unchanged','no_Git_mutation_or_publication':True}
(E/'source-and-output-audit.json').write_text(json.dumps(result,indent=2)+'\n')
print('PASS: 18 commands; 17 elaborated signatures; 66 standard-three reports; 115/139 actual project closures; 7 complete nested inventories; 361+31+17 preserved inputs')
