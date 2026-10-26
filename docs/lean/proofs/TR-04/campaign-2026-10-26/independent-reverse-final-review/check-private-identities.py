#!/usr/bin/env python3
"""Exercise two identical private source names in different actual modules."""
from pathlib import Path
from datetime import datetime,timezone
import ast,hashlib,json,os,re,subprocess,tempfile
BASE=Path(__file__).resolve().parent;REPO=BASE.parents[5]
LEAN=REPO.parent/'tooling/lean-4.33.1-darwin_aarch64/bin/lean'
PACKAGES=(REPO/'lean-statements/.lake/packages').resolve()
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
out=BASE/'private-identity-controls';out.mkdir(exist_ok=False)
tree=ast.parse((BASE/'replay.py').read_text())
preamble=next(ast.literal_eval(n.value) for n in tree.body if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='preamble' for t in n.targets))
a='''import LeanCert.Tactic.Verification
namespace IndependentIdentityFixture
private theorem same : True := True.intro
private theorem denied : True := True.intro
local instance localProof : NeZero (1 : Nat) := ⟨by decide⟩
def visible : Nat := 1
end IndependentIdentityFixture
'''
b='''import LeanCert.Tactic.Verification
namespace IndependentIdentityFixture
private theorem same : True := True.intro
axiom hiddenControlOnly : False
private theorem denied : False := hiddenControlOnly
end IndependentIdentityFixture
'''
imports='import PrivateTwinA\nimport PrivateTwinB\n'
positive=imports+preamble+'''
#audit_named "IndependentIdentityFixture.same" "PrivateTwinA" "private" "theorem"
#audit_named "IndependentIdentityFixture.same" "PrivateTwinB" "private" "theorem"
#audit_named "IndependentIdentityFixture.denied" "PrivateTwinA" "private" "theorem"
#audit_named "IndependentIdentityFixture.localProof" "PrivateTwinA" "local" "theorem"
#audit_named "IndependentIdentityFixture.visible" "PrivateTwinA" "public" "definition"
'''
negative=imports+preamble+'\n#audit_named "IndependentIdentityFixture.denied" "PrivateTwinB" "private" "theorem"\n'
wrong_module=imports+preamble+'\n#audit_named "IndependentIdentityFixture.same" "PrivateTwinAbsent" "private" "theorem"\n'
wrong_kind=imports+preamble+'\n#audit_named "IndependentIdentityFixture.same" "PrivateTwinA" "private" "definition"\n'
sources={'PrivateTwinA.lean':a,'PrivateTwinB.lean':b,'PrivatePositive.lean':positive,'PrivateNegative.lean':negative,
 'PrivateMissingModule.lean':wrong_module,'PrivateWrongKind.lean':wrong_kind}
for name,text in sources.items():(out/name).write_text(text)
commands=[]
with tempfile.TemporaryDirectory(prefix='objects-',dir=BASE) as tmp:
    fresh=Path(tmp)
    libs=[p/'.lake/build/lib/lean' for p in sorted(PACKAGES.iterdir()) if (p/'.lake/build/lib/lean').is_dir()]
    env=dict(os.environ,LEAN_PATH=os.pathsep.join(map(str,[fresh,*libs,LEAN.parent.parent/'lib/lean'])))
    for name,expected in [('PrivateTwinA.lean',0),('PrivateTwinB.lean',0),('PrivatePositive.lean',0),('PrivateNegative.lean',1),('PrivateMissingModule.lean',1),('PrivateWrongKind.lean',1)]:
        p=subprocess.run([str(LEAN),'-R',str(out),'-o',str(fresh/Path(name).with_suffix('.olean')),str(out/name)],cwd=out,env=env,text=True,capture_output=True)
        log=out/(name+'.log');log.write_text(p.stdout+p.stderr)
        commands.append({'source':name,'source_sha256':sha(out/name),'exit_code':p.returncode,'expected_exit_code':expected,'log':str(log.relative_to(REPO)),'log_sha256':sha(log)})
        assert p.returncode==expected,p.stdout+p.stderr
text=(out/'PrivatePositive.lean.log').read_text()
expected_ids=['_private.PrivateTwinA.0.IndependentIdentityFixture.same','_private.PrivateTwinB.0.IndependentIdentityFixture.same',
 '_private.PrivateTwinA.0.IndependentIdentityFixture.denied','IndependentIdentityFixture.localProof','IndependentIdentityFixture.visible']
kind_records=re.findall(r'AUDITED_KIND (\S+) (\S+)',text)
axiom_records=re.findall(r'AUDITED_AXIOMS (\S+) \[([^\]]*)\]',text)
actual_records=re.findall(r'AUDITED_ACTUAL (\S+) (\S+) (\S+)',text)
assert sorted(n for n,_ in kind_records)==sorted(expected_ids)
assert sorted(n for n,_ in axiom_records)==sorted(expected_ids)
assert sorted(n for _,n,_ in actual_records)==sorted(expected_ids)
assert len({n for n,_ in kind_records})==5
assert [u for u,_,_ in actual_records].count('IndependentIdentityFixture.same')==2
assert all(set(a.strip() for a in xs.split(',') if a.strip())<={'propext','Classical.choice','Quot.sound'} for _,xs in axiom_records)
assert 'depends on sorry or unrecognized axioms' in (out/'PrivateNegative.lean.log').read_text()
assert 'IndependentIdentityFixture.hiddenControlOnly' in (out/'PrivateNegative.lean.log').read_text()
assert 'missing exact compiler constant' in (out/'PrivateMissingModule.lean.log').read_text()
assert 'constant kind differs from frozen source' in (out/'PrivateWrongKind.lean.log').read_text()
result={'passed':True,'executed_utc':datetime.now(timezone.utc).isoformat(),'scope':'Auditor fixture only; none of the custom-axiom fixture proofs is an accepted NLA proof.',
 'driver_sha256':sha(BASE/'replay.py'),'checker_sha256':sha(Path(__file__)),'lean_sha256':sha(LEAN),
 'two_modules_with_same_private_source_name_checked_distinctly':True,'positive_actual_kernel_ids':expected_ids,
 'private_local_public_kinds_passed':True,'hidden_custom_axiom_in_exact_second_module_rejected':True,
 'wrong_module_rejected':True,'wrong_actual_kind_rejected':True,'negative_control_accepted_as_proof':False,
 'commands':commands,'proof_inputs_changed':False,'full_TR04_Target_proved':False}
(out/'result.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'passed':True,'sha256':sha(out/'result.json'),'negative_controls':'all three correctly rejected'},indent=2))
