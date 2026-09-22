#!/usr/bin/env python3
"""Development-only author typecheck; not a complete-problem verification."""
from pathlib import Path
import os
import subprocess

root = Path(__file__).resolve().parents[2]
evidence = Path(__file__).resolve().parent
build = Path('/private/tmp/nla-tr27-integral-image-final-build')
packages = Path('/private/tmp/nla-formalization-campaign-20260915/linear-systems-and-elimination/IE-15/lean/.lake/packages')
lean = Path('/private/tmp/nla-campaign-toolchain/lean-4.33.1-darwin_aarch64/bin/lean')
env = os.environ.copy()
env['LEAN_PATH'] = os.pathsep.join([str(build), str(root)] + [
    str(p / '.lake/build/lib/lean') for p in sorted(packages.iterdir()) if p.is_dir()])
with (evidence / 'development-typecheck.log').open('w') as log:
    log.write('Author development-only macOS typecheck; no full verification claim.\n')
    log.write(subprocess.check_output([str(lean), '--version'], text=True))
    for file in ['NLA/TR27/Definitions.lean', 'NLA/TR27/Algebra.lean',
                 'NLA/TR27/IntegralImage.lean',
                 'reviews/integral-image-author-evidence/Axioms.lean']:
        output = build / Path(file).with_suffix('.olean')
        output.parent.mkdir(parents=True, exist_ok=True)
        cmd = [str(lean), '-o', str(output), file]
        log.write('COMMAND: ' + ' '.join(cmd) + '\n')
        log.flush()
        result = subprocess.run(cmd, cwd=root, env=env, text=True,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        log.write(result.stdout + 'EXIT: ' + str(result.returncode) + '\n')
        log.flush()
        print(file, result.returncode, result.stdout, flush=True)
        if result.returncode:
            raise SystemExit(result.returncode)
