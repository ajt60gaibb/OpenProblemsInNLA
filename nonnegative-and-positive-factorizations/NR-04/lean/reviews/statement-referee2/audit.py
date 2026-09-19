"""Independent NR04 finite/source audit; no Lean, no submitted checker import."""
from pathlib import Path
from fractions import Fraction
from hashlib import sha256
from datetime import datetime, timezone
import json
import re
import subprocess

ROOT = Path(__file__).resolve().parents[2]
PACKET = ROOT / 'development/NR04-statements'
OUT = Path(__file__).resolve().parent
REPO = ROOT.parent

def digest(data):
    return sha256(data).hexdigest()

def rank(rows):
    a = [[Fraction(x) for x in r] for r in rows]
    r = 0
    for c in range(len(a[0])):
        p = next((p for p in range(r, len(a)) if a[p][c]), None)
        if p is None:
            continue
        a[r], a[p] = a[p], a[r]
        d = a[r][c]
        a[r] = [v / d for v in a[r]]
        for i in range(len(a)):
            if i != r:
                d = a[i][c]
                a[i] = [x - d * y for x, y in zip(a[i], a[r])]
        r += 1
    return r

inputs = [dict(path=str(p.relative_to(PACKET)), sha256=digest(p.read_bytes()),
               bytes=p.stat().st_size) for p in sorted(PACKET.rglob('*')) if p.is_file()]
bindings = json.loads((PACKET / 'SOURCE-BINDINGS.json').read_text())
bound_sources = []
for item in bindings['git_sources']:
    result = subprocess.run(['git', 'show', item['repository_commit'] + ':' + item['path']],
                            cwd=REPO, capture_output=True, check=True)
    data = result.stdout
    assert digest(data) == item['sha256'] and len(data) == item['bytes'], item['path']
    bound_sources.append(dict(path=item['path'], sha256=digest(data), bytes=len(data)))
handoff = json.loads((PACKET / 'SOURCE-AUTHOR-HANDOFF.json').read_text())
for item in handoff['source_files']:
    assert digest((PACKET / item['path']).read_bytes()) == item['sha256'], item['path']
challenge = (PACKET / 'Challenge.lean').read_text()
definitions = (PACKET / 'NLA/NR04/Definitions.lean').read_text()
names = ['NLA.NR04.' + x for x in re.findall(r'^theorem\s+(\w+)', challenge, re.M)]
config = json.loads((PACKET / 'comparator.json').read_text())
assert len(names) == 15 and names == config['theorem_names']
assert config['definition_names'] == []
assert set(config['permitted_axioms']) == {'propext', 'Classical.choice', 'Quot.sound'}
assert len(re.findall(r'^\s+sorry\s*$', challenge, re.M)) == 15
assert not re.search(r'^\s*(?:axiom|theorem)\b|:=\s*(?:by\s+)?sorry', definitions, re.M)
t = list(range(-4,5))
a = list(map(abs,t))
W = [[int(a[i] == r) if r < 5 else 2*max(t[i] if r == 5 else -t[i],0)
      for r in range(7)] for i in range(9)]
H = [[(r-a[j])**2 if r < 5 else 2*max(-t[j] if r == 5 else t[j],0)
      for j in range(9)] for r in range(7)]
D = [[(i-j)**2 for j in range(9)] for i in range(9)]
assert all(v >= 0 for row in W+H for v in row)
assert all(sum(W[i][r]*H[r][j] for r in range(7)) == D[i][j]
           for i in range(9) for j in range(9))
B = [row[:3] for row in D[:3]]
det = (B[0][0]*(B[1][1]*B[2][2]-B[1][2]*B[2][1])
       - B[0][1]*(B[1][0]*B[2][2]-B[1][2]*B[2][0])
       + B[0][2]*(B[1][0]*B[2][1]-B[1][1]*B[2][0]))
assert det == 8 and rank(D) == 3
assert all(0 <= x <= 4 for x in a)
yaml_argv = ['ruby','-e','require "yaml"; require "json"; puts JSON.pretty_generate(YAML.safe_load(File.read(ARGV[0]), aliases: false))',str(PACKET/'formalization.yaml')]
yr = subprocess.run(yaml_argv, capture_output=True, text=True)
(OUT/'yaml-parse.stdout').write_text(yr.stdout)
(OUT/'yaml-parse.stderr').write_text(yr.stderr)
receipt_path = ROOT/'local-lean/runs/recovery-028/RECEIPT.json'
receipt = json.loads(receipt_path.read_text())
lean_log = ROOT/'local-lean/runs/recovery-028/NLA.NR04.Definitions.log'
record = dict(
    timestamp_utc=datetime.now(timezone.utc).isoformat(),
    reviewer='/root/nr04_statement_referee',
    scope='Independent source, finite exact arithmetic and metadata audit only; no Lean compiler or Comparator executed by this reviewer',
    input_files=inputs, bound_source_hashes_verified=bound_sources,
    source_author_handoff_hashes_match=True, comparator_contract_names_match=True,
    exact_finite_witness=dict(product_entries_checked=81, determinant=det,
        rank_D=rank(D), rank_W=rank(W), rank_H=rank(H), nonnegative=True,
        caveat='Finite upper/rank diagnostic only; does not prove the geometric lower bound or any universal Lean theorem'),
    yaml_parse=dict(argv=yaml_argv, exit_code=yr.returncode,
        stdout_sha256=digest(yr.stdout.encode()),stderr_sha256=digest(yr.stderr.encode())),
    inspected_root_lean_evidence=dict(receipt=str(receipt_path),receipt_sha256=digest(receipt_path.read_bytes()),
        log=str(lean_log),log_sha256=digest(lean_log.read_bytes()),
        commands=[c for c in receipt['commands'] if 'NR04' in c.get('module','')]),
    independent_statement_approval=False, final_proof_review=False,
    lean_executed_by_reviewer=False, comparator_executed=False,
    whole_target_verified=False, count_change=0)
(OUT/'AUDIT.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(dict(status='audit completed; no statement approval',
    packet_files=len(inputs), bound_sources=len(bound_sources), contracts=len(names),
    exact_finite_witness=record['exact_finite_witness'], yaml_exit=yr.returncode),indent=2))
