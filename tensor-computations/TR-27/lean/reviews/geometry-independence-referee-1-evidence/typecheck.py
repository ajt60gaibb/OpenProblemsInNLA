#!/usr/bin/env python3
"""Independent cached development build; not authoritative Linux verification."""
from pathlib import Path
import os
import subprocess

root = Path(__file__).resolve().parents[2]
lean = Path('/private/tmp/nla-campaign-toolchain/lean-4.33.1-darwin_aarch64/bin/lean')
packages = Path('/private/tmp/nla-formalization-campaign-20260915/linear-systems-and-elimination/IE-15/lean/.lake/packages')
build = Path('/private/tmp/nla-tr27-geometry-independence-referee-1-fresh')
env = os.environ.copy()
env['LEAN_PATH'] = os.pathsep.join([str(build), str(root)] +
    [str(p / '.lake/build/lib/lean') for p in sorted(packages.iterdir()) if p.is_dir()])
files = [Path('NLA/TR27') / (m + '.lean') for m in
         ['Definitions', 'Algebra', 'IntegralImage', 'Geometry', 'Independence']]
files += [Path('reviews/geometry-independence-referee-1-evidence/BoundaryAndAxioms.lean')]
with (Path(__file__).parent / 'typecheck.log').open('w') as log:
    log.write('Independent development elaboration with cached dependencies; no Linux/Comparator claim.\n')
    log.write(subprocess.check_output([str(lean), '--version'], text=True))
    for source in files:
        output = build / source.with_suffix('.olean')
        output.parent.mkdir(parents=True, exist_ok=True)
        cmd = [str(lean), '-o', str(output), str(source)]
        log.write('COMMAND: ' + ' '.join(cmd) + '\n')
        log.flush()
        result = subprocess.run(cmd, cwd=root, env=env, text=True,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        log.write(result.stdout + 'EXIT: ' + str(result.returncode) + '\n')
        log.flush()
        print(str(source), result.returncode, result.stdout, flush=True)
        if result.returncode:
            raise SystemExit(result.returncode)
