from pathlib import Path
import re,json
p=Path('/private/tmp/nla-campaign-existing-review/IE14-final-source/snapshot')
names=[]
for f in sorted((p/'NLA/IE14').glob('*.lean')):
 names += ['NLA.IE14.'+n for n in re.findall(r'^(?:theorem|lemma)\s+(\w+)',f.read_text(),re.M)]
(p/'FinalAudit.lean').write_text('import Solution\nimport LeanCert.Tactic\n\n'+''.join(f'#assert_trust kernel {n}\n#print axioms {n}\n' for n in names))
config=json.loads(Path('/private/tmp/nla-formalization-ie14-20260915/linear-systems-and-elimination/IE-14/lean/comparator.json').read_text())
for mode in ['Challenge','Solution']:
 (p/f'{mode}Types.lean').write_text(f'import {mode}\nset_option pp.all true\n'+''.join(f'#check {n}\n' for n in config['theorem_names']))
(p/'DependencyAudit.lean').write_text('''import Solution
import Lean.Util.FoldConsts
open Lean Elab Command
run_cmd do
  let env ← getEnv
  for root in [``NLA.IE14.witness_data, ``NLA.IE14.witness_attainment, ``NLA.IE14.canonical_result] do
    let mut pending := [root]
    let mut seen : List Name := []
    while !pending.isEmpty do
      let name := pending.head!
      pending := pending.tail!
      if !seen.contains name then
        seen := name :: seen
        let some ci := env.find? name | throwError "Missing constant {name}"
        let dependencies := ci.type.getUsedConstants ++
          ((ci.value? (allowOpaque := true)).map Expr.getUsedConstants).getD #[]
        for child in dependencies do
          if child.toString.startsWith "NLA.IE14." then
            pending := child :: pending
    for required in [``NLA.IE14.half_complex_ne_zero, ``NLA.IE14.norm_half_complex_le_one,
                     ``NLA.IE14.half_bounds_certificate] do
      unless seen.contains required do
        throwError "Missing {required} in {root} actual compiled expression closure"
    logInfo m!"{root}: BOTH numerical helper branches and kernel certificate present in actual compiled dependency closure ({seen.length} project constants)"
#print NLA.IE14.half_complex_ne_zero
#print NLA.IE14.norm_half_complex_le_one
''')
(p.parent/'audited-theorems.json').write_text(json.dumps(names,indent=2)+'\n')
print('Generated audits for',len(names),'theorems and',len(config['theorem_names']),'public types')
