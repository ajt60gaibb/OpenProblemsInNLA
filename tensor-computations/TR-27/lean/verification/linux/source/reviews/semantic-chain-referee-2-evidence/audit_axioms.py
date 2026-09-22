#!/usr/bin/env python3
"""Independent local axiom audit of the generic semantic chain, after fresh rebuild."""
from pathlib import Path
import os
import subprocess
root = Path(__file__).resolve().parents[2]
evidence = Path(__file__).resolve().parent
build = Path('/private/tmp/nla-tr27-semantic-chain-referee-2-build')
packages = Path('/private/tmp/nla-formalization-campaign-20260915/linear-systems-and-elimination/IE-15/lean/.lake/packages')
lean = Path('/private/tmp/nla-campaign-toolchain/lean-4.33.1-darwin_aarch64/bin/lean')
env = os.environ.copy()
env['LEAN_PATH'] = os.pathsep.join([str(build), str(root)] + [
    str(p / '.lake/build/lib/lean') for p in sorted(packages.iterdir()) if p.is_dir()])
command = [str(lean), 'reviews/semantic-chain-referee-2-evidence/Axioms.lean']
r = subprocess.run(command, cwd=root, env=env, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
(evidence / 'axioms.log').write_text('Independent local cached-dependency axiom audit.\nCOMMAND: ' + ' '.join(command) + '\n' + r.stdout + 'EXIT: ' + str(r.returncode) + '\n')
print(r.stdout)
raise SystemExit(r.returncode)
