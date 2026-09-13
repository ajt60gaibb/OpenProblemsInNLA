from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, os, subprocess

R = Path('/tmp/nla-lean-ra09-worktree')
E = R/'randomized-and-low-rank-approximation/RA-09'
O = E/'lean/verification/publication-2026-09-13'
D = O/'initial-layout'
D.mkdir()
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
before = {}
for n in ['README.md', 'problem.tex', 'problem.pdf']:
    (D/n).write_bytes((E/n).read_bytes())
    before[n] = sha(E/n)
s = (E/'README.md').read_text()
old = 'tools/lean/verify.sh randomized-and-low-rank-approximation/RA-09/lean \\\n  /tmp/nla-ra09-check'
new = 'tools/lean/verify.sh \\\n  randomized-and-low-rank-approximation/RA-09/lean \\\n  /tmp/nla-ra09-check'
assert s.count(old) == 1
original = s[s.index('Let $`n\\ge2`$'):]
s = s.replace(old, new, 1)
assert s[s.index('Let $`n\\ge2`$'):] == original
(E/'README.md').write_text(s)
env = os.environ.copy()
env['PANDOC'] = '/tmp/nla-submission-tools/pandoc-3.11-arm64/bin/pandoc'
env['XELATEX'] = '/Library/TeX/texbin/xelatex'
checks = []
for label, args in [('format-final', ['python3', 'tools/format_math.py', '--check']), ('render-final', ['python3', 'tools/render_problems.py', 'RA-09'])]:
    r = subprocess.run(args, cwd=R, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (O/(label+'.log')).write_bytes(r.stdout)
    checks.append({'command': args, 'exit_code': r.returncode, 'raw_log': label+'.log', 'log_sha256': sha(O/(label+'.log'))})
    assert r.returncode == 0 and b'Overfull' not in r.stdout, r.stdout.decode()
V = Path('/tmp/nla-lean-formalization/ra09-publication-pages-final')
V.mkdir()
subprocess.run(['/opt/homebrew/bin/pdftoppm', '-scale-to', '1400', '-png', str(E/'problem.pdf'), str(V/'page')], check=True)
record = {'utc': datetime.now(timezone.utc).isoformat(), 'reason': 'Initial actual render reported a 30.76022pt overfull verbatim line. Root viewed all three pages; the final command is wrapped over three equivalent shell continuation lines.', 'before': before, 'after': {n:sha(E/n) for n in before}, 'original_target_suffix_unchanged': True, 'checks': checks, 'pages': {str(f):sha(f) for f in sorted(V.glob('*.png'))}, 'final_visual_review': 'pending display', 'marker_scope': 'Same recorded publication edit operation; no additional marker or invented earlier timing.'}
(O/'layout-correction.json').write_text(json.dumps(record, indent=2)+'\n')
(O/'fix_layout.py').write_bytes(Path(__file__).read_bytes())
print(json.dumps(record, indent=2))
