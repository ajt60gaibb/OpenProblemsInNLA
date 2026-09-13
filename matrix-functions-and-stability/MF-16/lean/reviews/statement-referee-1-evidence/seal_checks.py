#!/usr/bin/env python3
"""Independent statement-stage integrity and evidence postchecks; no build."""
import hashlib
import json
import re
import subprocess
from datetime import datetime, timezone
from pathlib import Path

E=Path(__file__).resolve().parent
P=E.parent.parent
R=P.parents[2]
D=Path('/tmp/nla-lean-mi22-worktree/matrix-inequalities-and-norms/MI-22/lean/.lake/packages')
S=Path('/tmp/nla-lean-formalization/standards')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def git(root,*args):return subprocess.check_output(['git','-C',str(root),*args]).decode().strip()
def save(name,value):(E/name).write_text(json.dumps(value,indent=2)+'\n')

f=json.loads((P/'reviews/statement-freeze.json').read_text())
assert sha(P/'reviews/statement-freeze.json')=='eaba8311f143727f2061f2b4c945e403e62b7e9041712d983ef56ccf2e7f0587'
assert sha(P/'reviews/statement-handoff.md')=='a97494a7b6ec59c1837e6fb100c98eddf79b7d18939d7cb9f606fa05b696bf7f'
assert len(f['files'])==45 and len(f['source_files'])==14
for name,digest in f['files'].items():assert sha(P/name)==digest,name
sources=[]
for name,digest in f['source_files'].items():
    blob=subprocess.check_output(['git','-C',str(R),'show',f['base']+':'+name])
    blobid=git(R,'rev-parse',f['base']+':'+name)
    assert sha(R/name)==hashlib.sha256(blob).hexdigest()==digest,name
    assert blobid==f['source_git_blobs'][name],name
    sources.append({'path':name,'sha256':digest,'git_blob':blobid})
authored=(R/'references/colbrook-matrix-functions-2026-09-11/manuscripts/MF-16.tex').read_text()
reviewed=(R/'references/colbrook-matrix-functions-2026-09-11/reviewed-sources/MF-16.tex').read_text()
assert authored.split('% BEGIN REVIEWED BODY',1)[1].split('% END REVIEWED BODY',1)[0].strip()==reviewed.split('\\maketitle',1)[1].strip()

fresh=json.loads((E/'fresh-checks.json').read_text())
assert len(fresh['commands'])==3 and fresh['pins_and_sources_rechecked_after']
for c in fresh['commands']:
    assert c['exit_code']==0 and sha(E/c['log'])==c['log_sha256']
    assert sha(P/c['source'])==sha(E/c['source_snapshot'])==c['sha256']
    assert 'error' not in (E/c['log']).read_text().lower()
assert not (E/'NLA-MF16-Definitions.log').read_text()
clog=(E/'Challenge.log').read_text()
assert clog.count('warning: declaration uses `sorry`')==9
assert len(clog.strip().splitlines())==9
inspection=(E/'reviews-statement-referee-1-evidence-Inspect.log').read_text()
assert 'warning:' not in inspection
audit_lines=[line for line in inspection.splitlines() if 'depends on axioms:' in line or 'does not depend on any axioms' in line]
assert len(audit_lines)==10
for line in audit_lines:
    if 'does not depend' in line:continue
    names=set(line.split('[',1)[1].rstrip(']').split(', '))
    assert names <= {'propext','Classical.choice','Quot.sound'}
for token in ['Complex.partialOrder','Matrix.PosDef','Matrix.IsHermitian','List.prod',
              'Matrix.instMulOfFintypeOfAddCommMonoid','Complex.ofReal','SystemZero','FinBoxMem']:
    assert token in inspection,token
challenge=(P/'Challenge.lean').read_text()
names=['NLA.MF16.'+name for name in re.findall(r'^theorem\s+(\w+)',challenge,re.M)]
config=json.loads((P/'comparator.json').read_text())
assert len(names)==9 and names==config['theorem_names']
assert config['definition_names']==[]
assert config['permitted_axioms']==['propext','Classical.choice','Quot.sound']
assert all(re.search(r'^'+re.escape(name)+r'(?:[.{\s]|$)',inspection,re.M) for name in names)
assert len(re.findall(r'^\s+sorry\s*$',challenge,re.M))==9
definitions=(P/'NLA/MF16/Definitions.lean').read_text()
assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe|run_tac)\b',definitions)
assert not (P/'Solution.lean').exists() and not (P/'NLA/MF16/Proof.lean').exists()
assert 'defaultTargets = ["Challenge"]' in (P/'lakefile.toml').read_text()
assert 'name = "Solution"' in (P/'lakefile.toml').read_text()
for pin in fresh['pins']:
    assert git(Path(pin['path']),'rev-parse','HEAD')==pin['expected']
    assert not git(Path(pin['path']),'status','--porcelain')
exact=json.loads((E/'exact-checks.json').read_text())
assert exact['Definitions_sha256']==sha(P/'NLA/MF16/Definitions.lean')
assert exact['actual_inspector_log_sha256']==sha(E/'reviews-statement-referee-1-evidence-Inspect.log')
assert exact['all_support_center_det_contraction_selfmap_checks']

api_files={
 'leancert':['LeanCert/Engine/RootFinding/Krawczyk.lean','LeanCert/Core/Support.lean',
             'LeanCert/Engine/Optimization/Gradient.lean','LeanCert/Examples/Krawczyk.lean',
             'LeanCert/Tactic/Verification.lean'],
 'mathlib':['Mathlib/Analysis/Complex/Order.lean','Mathlib/LinearAlgebra/Matrix/PosDef.lean',
            'Mathlib/LinearAlgebra/Matrix/Charpoly/Basic.lean','Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean']}
apis={}
for package,files in api_files.items():
    for name in files:
        root=D/package
        apis[package+'/'+name]={'sha256':sha(root/name),'bytes':(root/name).stat().st_size,
                              'commit':git(root,'rev-parse','HEAD'),'git_blob':git(root,'rev-parse','HEAD:'+name)}
commit_file=S/'TauCetiProject_TauCetiReview-commit.json'
tree_file=S/'TauCetiProject_TauCetiReview-tree.json'
commit=json.loads(commit_file.read_text());tree=json.loads(tree_file.read_text())
assert commit['sha']==tree['sha']=='afb424eda89e8ac96d9eb69f6a88972055a4cd1b' and not tree['truncated']
tree_blobs={row['path']:row['sha'] for row in tree['tree'] if row['type']=='blob'}
rubrics={}
rubric_root=S/'sources/TauCetiProject/TauCetiReview'
for path in sorted((rubric_root/'rubrics').glob('*.md')):
    data=path.read_bytes();name=str(path.relative_to(rubric_root))
    blob=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
    assert blob==tree_blobs[name]
    rubrics[name]={'sha256':sha(path),'bytes':len(data),'git_blob':blob}
assert len(rubrics)==12
save('actual-api-rubric-inputs.json',{
 'api_read_scope':'Actual relevant declarations and surrounding proof/implementation, not a claim that every complete library module was read.',
 'apis':apis,'rubric_commit':commit['sha'],'rubrics':rubrics,
 'rubric_scope':'All twelve complete rubrics read in this review session; applied through repository protocol. Retained receipt/blob comparison, no fresh network fetch or official service run.',
 'rubric_commit_receipt_sha256':sha(commit_file),'rubric_tree_receipt_sha256':sha(tree_file),
 'repository_review_sha256':sha(R/'docs/lean/REVIEW.md'),
 'repository_review_git_blob':git(R,'rev-parse',f['base']+':docs/lean/REVIEW.md')})
save('final-input-audit.json',{
 'reviewer':'/root/solved_statement_inventory','utc':datetime.now(timezone.utc).isoformat(),
 'verdict':'PASS: frozen statement fidelity and independent diagnostics only',
 'statement_freeze_sha256':sha(P/'reviews/statement-freeze.json'),
 'handoff_sha256':sha(P/'reviews/statement-handoff.md'),'source_base':f['base'],
 'frozen_project_count':45,'frozen_project_bytes_unchanged':True,
 'original_sources_count':14,'original_sources_unchanged':sources,
 'authored_reviewed_mathematical_body_match':True,
 'fresh_final_commands_all_pass':True,'fresh_final_command_count':3,
 'preserved_prior_referee_attempt':'attempt-before-Boolean-print; candidate Definitions and Challenge passed; the inspector alone required decide around its diagnostic Prop before ToString.',
 'intended_Challenge_holes':9,'other_final_warnings':0,
 'structural_and_library_standard_three_or_subset_checks':audit_lines,
 'actual_nine_Challenge_and_Comparator_names':names,'no_definition_exceptions':True,
 'actual_checker_diagnostic':True,'exact_fraction_interval_reconstruction':True,
 'all_ten_dependency_pins_clean_after':True,
 'formalization_metadata_scope':'No formalization.yaml exists at statement stage. Actual v0.4 completion metadata remains a later required packaging gate, not claimed here.',
 'no_Proof_or_Solution':True,
 'fresh_checks_sha256':sha(E/'fresh-checks.json'),
 'exact_checks_sha256':sha(E/'exact-checks.json'),
 'actual_inspector_sha256':sha(E/'reviews-statement-referee-1-evidence-Inspect.log'),
 'limitations':'No candidate kernel Boolean proof, root theorem implementation, Linux/Comparator/default-kernel/control result or canonical promotion.'})
print('PASS: 45 frozen inputs + 14 Git sources unchanged; 9 exact contracts, 3 final fresh commands, 10 structural/library standard-three-or-subset checks, exact interval/matrix diagnostics.')
