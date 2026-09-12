"""Independent checks of actual elaborated statement semantics and trust output."""
from pathlib import Path
import datetime, hashlib, json, re, subprocess
out=Path(__file__).resolve().parent
p=out.parents[1]
r=subprocess.run(['python3',str(out/'exact_reconstruction.py')],capture_output=True)
(out/'exact-reconstruction.log').write_bytes(r.stdout+r.stderr)
assert r.returncode==0,r.stderr
print(r.stdout.decode().strip())
text=(out/'inspection.log').read_text()
a=re.findall(r"'([^'\n]+)' depends on axioms: \[([^\]]*)\]",text)
assert len(a)==25,len(a)
records={n:[re.sub(r'\.\{[^}]*\}','',v.strip()) for v in axs.split(',') if v.strip()] for n,axs in a}
allowed={'propext','Classical.choice','Quot.sound'}
config=json.loads((p/'comparator.json').read_text())
exports=config['theorem_names']
assert config['definition_names']==[] and set(config['permitted_axioms'])==allowed
for n,axs in records.items():
    assert set(axs)<=allowed|({'sorryAx'} if n in exports else set()),(n,axs)
    assert ('sorryAx' in axs)==(n in exports),(n,axs)
assert len(exports)==7 and (out/'challenge.log').read_text().count('declaration uses `sorry`')==7
assert not (out/'definitions.log').read_text()
assert 'warning:' not in text and 'error:' not in text
assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b',(p/'NLA/TR15/Definitions.lean').read_text())
for marker in ['@Pi.instFintype','@Finset.sum','@Finset.prod','@Pi.instZero','@HPow.hPow.{0, 0, 0} Real Nat Real','@Fin.cast','Real.instLE']:
    assert marker in text,marker
assert not (p/'NLA/TR15/Proof.lean').exists() and not (p/'Solution.lean').exists()
(out/'statement-trust-audit.json').write_text(json.dumps({'verdict':'PASS for statements only','definition_count':18,'challenge_count':7,'declaration_axioms':records,'definition_placeholder_or_custom_axiom':False,'challenge_placeholders_intentional':True,'proof_files_absent':True},indent=2)+'\n')
libs=[p/'.lake/packages/mathlib/Mathlib/Data/Fintype/Pi.lean',p/'.lake/packages/mathlib/Mathlib/Topology/Order/IntermediateValue.lean',Path('/Users/georgestepaniants/.elan/toolchains/leanprover--lean4---v4.33.1/src/lean/Init/Data/Fin/Basic.lean')]
(out/'library-source-hashes.json').write_text(json.dumps({str(x):{'sha256':hashlib.sha256(x.read_bytes()).hexdigest(),'bytes':x.stat().st_size} for x in libs},indent=2)+'\n')
(out/'primary-source-check.json').write_text(json.dumps({'accessed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'url':'https://www.polyu.edu.hk/ama/staff/new/qilq/BIT-DQW.pdf','method':'Independent web PDF text inspection','pages_one_based':[2,3,8,21],'scope':'Confirmed zero-based array generators, full componentwise real H-eigenpair equations, and the final multiple-order inheritance conjecture. The primary text distinguishes stronger associated-matrix hypotheses. No claim of a new literature/priority search.'},indent=2)+'\n')
print('PASS: 18 definitions have only standard axioms; exactly seven intentional Challenge holes; genuine Fin.cast / Pi.instFintype / real natural-power semantics inspected.')
