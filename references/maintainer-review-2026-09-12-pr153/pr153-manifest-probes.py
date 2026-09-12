#!/usr/bin/env python3
"""Independent metadata/path probes. Never compiles or runs candidate Lean."""
import contextlib
import copy
import hashlib
import importlib.util
import io
import json
from pathlib import Path
import sys
import tempfile
import yaml

sys.dont_write_bytecode = True
root = Path('/private/tmp/nla-pr153')
spec = importlib.util.spec_from_file_location('reviewed_manifest', root/'tools/lean/validate_manifest.py')
validator = importlib.util.module_from_spec(spec)
spec.loader.exec_module(validator)
schema = json.loads((root/'docs/lean/schema/v0.4.schema.json').read_text())
config = dict(challenge_module='Challenge', solution_module='Solution',
              theorem_names=['Result'], definition_names=[],
              permitted_axioms=['propext','Classical.choice','Quot.sound'])
metadata = dict(version='v0.4', project=dict(name='Probe',authors=['Reviewer'],license='Apache-2.0'),
    sources=[dict(title='Fixture',type='original-proof')], automation=dict(methods=[dict(method='manual')]),
    review=dict(status='unchecked'), status=dict(sorry_count=0,sorry_in_definitions=0,axioms=[],
    main_results=[dict(declaration='Result',file='Solution.lean',sorry_count=0,axioms=[],comparator_config='comparator.json')]))
results=[]
def probe(name,mutate,expected):
    with tempfile.TemporaryDirectory(prefix='nla-pr153-manifest-',dir='/private/tmp') as td:
        parent=Path(td)
        project=parent/'project'
        project.mkdir()
        (project/'Solution.lean').write_text('-- source fixture\n')
        (parent/'outside.lean').write_text('-- outside source fixture\n')
        (project/'alias.lean').symlink_to(parent/'outside.lean')
        md,cfg=copy.deepcopy(metadata),copy.deepcopy(config)
        mutate(md,cfg,project,parent)
        (project/'formalization.yaml').write_text(yaml.safe_dump(md))
        (project/'comparator.json').write_text(json.dumps(cfg))
        try:
            with contextlib.redirect_stdout(io.StringIO()):
                validator.validate(project,schema)
            accepted,error=True,None
        except Exception as exc:
            accepted,error=False,type(exc).__name__+': '+str(exc).splitlines()[0]
        results.append(dict(case=name,accepted=accepted,expected_accept=expected,
                            expectation_met=accepted==expected,error=error))

probe('ordinary valid consistent metadata',lambda *args:None,True)
probe('parent traversal source',lambda md,cfg,p,par:md['status']['main_results'][0].update(file='../outside.lean'),False)
probe('absolute external source',lambda md,cfg,p,par:md['status']['main_results'][0].update(file=str(par/'outside.lean')),False)
probe('symlink source escape',lambda md,cfg,p,par:md['status']['main_results'][0].update(file='alias.lean'),False)
probe('absent source',lambda md,cfg,p,par:md['status']['main_results'][0].update(file='absent.lean'),False)
probe('boolean false instead of integer zero',lambda md,cfg,p,par:md['status'].update(sorry_count=False),False)
probe('missing completed status',lambda md,cfg,p,par:md.pop('status'),False)
probe('duplicate result declaration',lambda md,cfg,p,par:md['status']['main_results'].append(copy.deepcopy(md['status']['main_results'][0])),False)
probe('result absent from comparator',lambda md,cfg,p,par:cfg.update(theorem_names=['Different']),False)
probe('wrong comparator reference',lambda md,cfg,p,par:md['status']['main_results'][0].update(comparator_config='../comparator.json'),False)
probe('custom result axiom',lambda md,cfg,p,par:md['status']['main_results'][0].update(axioms=['AssumedTarget']),False)
result=dict(scope='Metadata consistency and result-file containment only; no proof truth or sandbox claim.',
            schema_sha256=hashlib.sha256((root/'docs/lean/schema/v0.4.schema.json').read_bytes()).hexdigest(),
            all_expectations_met=all(x['expectation_met'] for x in results),cases=results)
Path('/private/tmp/nla-review-trace/pr153-manifest-probes.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
