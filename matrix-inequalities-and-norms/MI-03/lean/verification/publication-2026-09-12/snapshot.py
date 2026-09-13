from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, subprocess

repo = Path('/tmp/nla-lean-mi03-worktree')
project = repo / 'matrix-inequalities-and-norms/MI-03/lean'
work = Path(__file__).resolve().parent
revision = '901ba5ffad3b57557b60c7360df67659d8b8aa21'
base = 'f41f1f9ffa2171550d4bb795862c6170c4f26070'
git = lambda *a: subprocess.check_output(['git', *a], cwd=repo)
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
assert git('rev-parse', 'HEAD').decode().strip() == revision
assert git('rev-parse', 'nla-upstream/main').decode().strip() == base
linux = project / 'verification/linux-2026-09-12'
receipts = list((linux/'artifacts/lean-MI-03').glob('*/result.json'))
assert len(receipts) == 1
receipt = json.loads(receipts[0].read_text())
assert receipt['repository_commit'] == revision and receipt['result'] == 'comparator-accepted'
inputs = receipt['input_sha256']
prefix = str(project.relative_to(repo)) + '/'
tracked = {p.removeprefix(prefix) for p in git('ls-tree', '-r', '--name-only', revision, '--', prefix).decode().splitlines()}
assert set(inputs) == tracked and len(inputs) == 173
for name, h in inputs.items():
    assert sha(project/name) == h, name
    assert hashlib.sha256(git('show', revision+':'+prefix+name)).hexdigest() == h, name
out = linux/'EVIDENCE-MANIFEST.json'
ev = json.loads(out.read_text())
actual = {str(p.relative_to(linux)) for p in linux.rglob('*') if p.is_file() and p != out}
assert actual == set(ev['files']) and len(actual) == 303
for name, r in ev['files'].items():
    assert sha(linux/name) == r['sha256'] and (linux/name).stat().st_size == r['bytes'], name
ops = {str(p.relative_to(project)): sha(p) for p in linux.rglob('*') if p.is_file()}
assert len(ops) == 304
sources = ['matrix-inequalities-and-norms/MI-03/'+name for name in ['README.md','solution.md','solution.tex','solution.pdf']]
for p in sources+['problem_ids.json']:
    assert git('show', revision+':'+p) == git('show', base+':'+p), p
tool_diff = git('diff', revision, base, '--', 'tools/lean', '.github/workflows/lean-verification.yml').decode()
assert not tool_diff
record = {'created_utc':datetime.now(timezone.utc).isoformat(), 'verified_revision':revision,
          'upstream_base':base, 'upstream_query':'git ls-remote https://github.com/ajt60gaibb/OpenProblemsInNLA.git refs/heads/main',
          'upstream_query_result':base+'\trefs/heads/main', 'verified_run':34722618003,
          'verified_inputs':inputs, 'operational_files':ops, 'shared_tools_diff':tool_diff,
          'canonical_and_source_unchanged_between_candidate_and_upstream':True,
          'preintegration_status':git('status','--short').decode()}
(work/'before-integration.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({'result':'PASS','verified_inputs':len(inputs),'operational_files':len(ops),'base':base}))
