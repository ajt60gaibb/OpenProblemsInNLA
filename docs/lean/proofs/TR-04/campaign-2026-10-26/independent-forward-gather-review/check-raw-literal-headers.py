#!/usr/bin/env python3
"""Check that recorded literal headers also match raw frozen source bytes."""
from pathlib import Path
from datetime import datetime,timezone
import ast,hashlib,json,re
BASE=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
c=json.loads((BASE/'source-lock.json').read_text())
run=BASE/'run-attempt-1'
bindings=json.loads((run/'consumer-bindings.json').read_text())
tree=ast.parse((BASE/'replay.py').read_text())
function=next(n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=='literal')
lookup={d['name']:d for b in c['blocks'] for d in b['declarations']}
frozen={r['path'].removeprefix('lean-statements/'):(run/'sources'/r['path'].removeprefix('lean-statements/')).read_bytes() for r in c['union']}
env={'lookup':lookup,'frozen':frozen,'without_comments':lambda s:s,'sha':sha,'re':re}
exec(compile(ast.Module(body=[function],type_ignores=[]),'<raw-header-check>','exec'),env)
records=[]
for b in c['blocks']:
    observed=bindings[b['key']]['literal_examples']
    assert [r['name'] for r in observed]==b['literal_endpoints']
    for r in observed:
        _,raw=env['literal'](r['name'])
        assert raw==r,(r,raw)
        records.append(dict(raw,block=b['key'],raw_source_sha256=sha(frozen[raw['source']])))
out={'passed':True,'executed_utc':datetime.now(timezone.utc).isoformat(),'scope':'Read-only raw binder/type header byte and theorem-application binding check; no new Lean replay.',
 'driver_sha256':sha((BASE/'replay.py').read_bytes()),'source_lock_sha256':sha((BASE/'source-lock.json').read_bytes()),
 'records':records,'header_count':len(records),'comments_or_strings_removed_from_any_recorded_header':False,
 'checker_sha256':sha(Path(__file__).read_bytes()),'proof_inputs_changed':False,'full_TR04_Target_proved':False}
(BASE/'raw-literal-header-check.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'passed':True,'headers':len(records),'sha256':sha((BASE/'raw-literal-header-check.json').read_bytes())},indent=2))
