"""Read-only final statement/config/source/pin checks for referee 2."""
from pathlib import Path
import hashlib,json,re,subprocess

out=Path(__file__).resolve().parent
project=out.parents[1]
repo=project.parents[2]
cache=Path('/tmp/nla-lean-mi22-worktree/matrix-inequalities-and-norms/MI-22/lean')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
write=lambda name,obj:(out/name).write_text(json.dumps(obj,indent=2)+'\n')
git=lambda path,*a:subprocess.check_output(['git','-C',str(path),*a])
freeze=json.loads((project/'reviews/statement-freeze.json').read_text())
assert sha(project/'reviews/statement-freeze.json')=='8c940e34c5d97c8b00d5560fe881416b7e5bbc563a005ed214db9bd54ad71d6b'
assert sha(project/'reviews/statement-handoff.md')=='e5e86598564e1e89d5668f56593e0048be62f22c2895332d3787e949df504c02'
for rel,expected in freeze['files'].items():assert sha(project/rel)==expected,rel
sources={}
for rel,expected in freeze['source_files'].items():
    assert sha(repo/rel)==expected,rel
    assert (repo/rel).read_bytes()==git(repo,'show',freeze['base']+':'+rel),rel
    sources[rel]={'sha256':expected,'git_blob':git(repo,'rev-parse',freeze['base']+':'+rel).decode().strip()}
write('original-source-identity.json',{'base':freeze['base'],'sources':sources})
assert not (project/'Solution.lean').exists() and not (project/'NLA/IV06/Proof.lean').exists()
definitions=(project/'NLA/IV06/Definitions.lean').read_text()
stripped=re.sub(r'/\-.*?\-/','',definitions,flags=re.S)
assert not re.search(r'\b(axiom|sorry|admit|unsafe|native_decide|implemented_by|extern)\b',stripped)
assert not re.search(r'^\s*(instance|local instance|scoped instance)\b',stripped,re.M)
challenge=(project/'Challenge.lean').read_text()
names=re.findall(r'^theorem\s+(\w+)\b',challenge,re.M)
assert len(names)==8 and challenge.count('  sorry\n')==8
config=json.loads((project/'comparator.json').read_text())
assert config['theorem_names']==['NLA.IV06.'+name for name in names]
assert config['theorem_names']==freeze['export_names']
assert config['definition_names']==[]
assert config['permitted_axioms']==['propext','Classical.choice','Quot.sound']
write('statement-config.json',{'result':'PASS','config':config,'definitions_sha256':sha(project/'NLA/IV06/Definitions.lean'),'Challenge_sha256':sha(project/'Challenge.lean'),'no_new_topological_or_matrix_instances':True,'no_implementation_exists':True,'warning':'All eight Challenge bodies are deliberate holes; no proof claim'})

package_paths={
 'mathlib':[
  'Mathlib/LinearAlgebra/Matrix/ToLinearEquiv.lean',
  'Mathlib/Topology/Connected/Basic.lean',
  'Mathlib/Topology/Connected/Clopen.lean',
  'Mathlib/Topology/Order/IntermediateValue.lean',
  'Mathlib/Topology/UniformSpace/Real.lean',
  'Mathlib/Topology/MetricSpace/Pseudo/Defs.lean',
  'Mathlib/SetTheory/Cardinal/Defs.lean',
  'Mathlib/SetTheory/Cardinal/Order.lean'],
 'leancert':['LeanCert/Tactic/Verification.lean']}
manifest=json.loads((project/'lake-manifest.json').read_text())
pins={p['name']:p['rev'] for p in manifest['packages']}
primary={}
for package,paths in package_paths.items():
    root=cache/'.lake/packages'/package
    for rel in paths:
        assert (root/rel).read_bytes()==git(root,'show',pins[package]+':'+rel)
        primary[package+'/'+rel]={'sha256':sha(root/rel),'revision':pins[package],'matches_immutable_git_blob':True}
write('primary-library-inputs.json',primary)
for name,rev in pins.items():
    root=cache/'.lake/packages'/name
    assert git(root,'rev-parse','HEAD').decode().strip()==rev
    assert not git(root,'status','--porcelain=v1').strip()

standards=Path('/tmp/nla-lean-formalization/standards')
standard_manifest=json.loads((standards/'MANIFEST.json').read_text())
rubrics={}
for angle in ['scope','correctness','proof-quality','reuse','generality','api-design','naming','placement','documentation','attribution']:
    rel='sources/TauCetiProject/TauCetiReview/rubrics/'+angle+'.md'
    assert sha(standards/rel)==standard_manifest[rel]['sha256']
    rubrics[angle]=standard_manifest[rel]
write('review-standard-inputs.json',{'pinned_Tau_Ceti_revision':'afb424eda89e8ac96d9eb69f6a88972055a4cd1b','rubrics':rubrics,'NLA_adaptation_sha256':sha(repo/'docs/lean/REVIEW.md'),'scope':'Independent AI statement review through repository adaptation, not official Tau Ceti service'})
search=['rg','-n','connected.*Icc|Icc.*connected|exists_mulVec_eq_zero_iff|mk_le_of_injective',
 '.lake/packages/mathlib/Mathlib/Topology/Connected',
 '.lake/packages/mathlib/Mathlib/Topology/Order',
 '.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/ToLinearEquiv.lean',
 '.lake/packages/mathlib/Mathlib/SetTheory/Cardinal/Order.lean']
r=subprocess.run(search,cwd=cache,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
assert r.returncode==0
(out/'reuse-search.log').write_bytes(r.stdout)
write('reuse-search.json',{'command':search,'exit_code':0,'log_sha256':sha(out/'reuse-search.log'),'assessment':'The planned determinant, preconnected-component/continuous-image/order-convexity, and cardinal injection bridges use actual existing Mathlib APIs; no custom topology/counting replacement needed.'})
assert json.loads((out/'fresh-result.json').read_text())['result']=='PASS'
assert json.loads((out/'reconstruction.json').read_text())['result']=='PASS'
write('integrity-after.json',{'result':'PASS','frozen_project_inputs_unchanged':len(freeze['files']),'original_source_git_blobs_unchanged':len(sources),'ten_dependency_sources_clean':True,'fresh_statement_commands':3,'definition_kernel_assertions':3,'Challenge_holes':8,'no_source_or_mathematical_edits':True,'publication_or_Linux_claim':False,'files':{rel:sha(project/rel) for rel in freeze['files']}})
print('PASS: complete 32-file statement freeze and eight original Git sources preserved; eight exact configured exports; ten clean dependency pins; nine actual primary-library inputs')
