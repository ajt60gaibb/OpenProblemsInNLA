"""Scoped independent NR04 statement amendment audit; never invokes Lean."""
from pathlib import Path
from hashlib import sha256
from datetime import datetime, timezone
import json
import re
import subprocess
import jsonschema

ROOT = Path(__file__).resolve().parents[2]
OUT = Path(__file__).resolve().parent
OLD = ROOT/'development/NR04-statements'
NEW = ROOT/'development/NR04-statements-v2'
def digest(b):
    return sha256(b).hexdigest()
for file in ['Challenge.lean','NLA/NR04/Definitions.lean']:
    original = (OLD/file).read_text()
    amended = (NEW/file).read_text()
    stripped = amended.replace('import Mathlib.Data.Real.Basic\n','').replace('set_option autoImplicit false\n\n','')
    assert stripped == original, file
for file in ['NUMERICAL_TARGETS.md','NUMERICAL-FIRST.json','comparator.json']:
    assert (OLD/file).read_bytes() == (NEW/file).read_bytes()
handoff = json.loads((NEW/'SOURCE-AUTHOR-HANDOFF.json').read_text())
for item in handoff['source_files']:
    data = (NEW/item['path']).read_bytes()
    assert digest(data) == item['sha256'] and len(data) == item['bytes'], item['path']
argv=['ruby','-e','require "yaml"; require "json"; puts JSON.pretty_generate(YAML.safe_load(File.read(ARGV[0]), aliases: false))',str(NEW/'formalization.yaml')]
yr = subprocess.run(argv,capture_output=True,text=True,check=True)
(OUT/'v2-yaml-parse.stdout').write_text(yr.stdout)
(OUT/'v2-yaml-parse.stderr').write_text(yr.stderr)
parsed=json.loads(yr.stdout)
schema_path='matrix-functions-and-stability/MF-07/lean/sources/standards/mathlib-initiative/formalization.yaml/schema/v0.4.schema.json'
sr=subprocess.run(['git','show','71563f17926cd826a892c2bba0e294894ee57a5c:'+schema_path],cwd=ROOT.parent,capture_output=True,check=True)
assert digest(sr.stdout)=='25ff6b25ca4511635aff4443cf20480c15e59dddf19591c730950b442ea54fce'
jsonschema.validate(parsed,json.loads(sr.stdout))
names=['NLA.NR04.'+x for x in re.findall(r'^theorem\s+(\w+)',(NEW/'Challenge.lean').read_text(),re.M)]
config=json.loads((NEW/'comparator.json').read_text())
assert names==config['theorem_names'] and len(names)==15
assert not (NEW/'Solution.lean').exists()
record=dict(timestamp_utc=datetime.now(timezone.utc).isoformat(),
    reviewer='/root/nr04_statement_referee',scope='Scoped v1-to-v2 statement amendment and metadata checks only',
    source_files=[dict(path=str(p.relative_to(NEW)),sha256=digest(p.read_bytes()),bytes=p.stat().st_size)
        for p in sorted(NEW.rglob('*')) if p.is_file()],
    exact_amendments_only=True,mathematical_bodies_and_headers_unchanged=True,
    source_author_handoff_hashes_match=True,
    comparator_names_match=True,numerical_first_plan_unchanged=True,
    yaml=dict(argv=argv,exit_code=yr.returncode,stdout_sha256=digest(yr.stdout.encode()),stderr_sha256=digest(yr.stderr.encode())),
    schema=dict(validator='Python jsonschema.validate',source= schema_path,sha256=digest(sr.stdout),result='PASS'),
    local_lean_executed_by_reviewer=False,comparator_executed=False,
    statement_approval='pending root actual successful amended header elaboration',whole_target_verified=False,count_change=0)
(OUT/'AUDIT-v2.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(dict(exact_amendments_only=True,math_statements_unchanged=True,yaml_parse='PASS',yaml_schema='PASS',theorem_count=len(names)),indent=2))
